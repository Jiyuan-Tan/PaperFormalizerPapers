module
public import Papers.TbsNeuralCausalPi.Helpers.EstimationCandidateBounds
public import Papers.TbsNeuralCausalPi.Helpers.DiscreteWasserstein
/-! # Construction-derived carriers for the two-sample constraint estimate

The same compact box carries the true observational law, every restricted
candidate law, all simulated observations, and almost every actual sample.
Only the two separate sampling tails remain inputs to the final union bound.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: observationalLaw_estimationObservationBox
/-- For [a nonnegative bound](hyp:K), if [the model's observed variables and
latent blocks satisfy that bound](hyp:hK), then [its observational law assigns
probability one to the coordinate box with the common observation radius](goal). -/
lemma observationalLaw_estimationObservationBox (M : EuclideanSCM kind dims)
    (K : ℝ≥0) (hK : VariablesBoundedAt M K) :
    observationalLaw M {v | ∀ c, |v.ofLp c| ≤ estimationObservationRadius kind K} = 1 := by
  letI := observationalLaw_probability M
  apply le_antisymm prob_le_one
  calc
    1 = observationalLaw M {v | ∀ c, |v.ofLp c| ≤ (K : ℝ)} :=
      (observationalLaw_bounded_coordinates M K hK).symm
    _ ≤ _ := by
      apply measure_mono
      intro v hv c
      exact (hv c).trans
        (by exact_mod_cast estimationObservationRadius_ge (kind := kind) K)

-- @node: observationalSample_ae_estimationObservationBox
/-- For [a nonnegative bound](hyp:K), suppose [the model's variables satisfy
that bound](hyp:hK), [each observation is measurable](hyp:hsample), and [each has
the model's observational law](hyp:hlaw). Then [almost surely every coordinate
of every observation is bounded in absolute value by the common observation
radius](goal). -/
lemma observationalSample_ae_estimationObservationBox
    {Omega : Type*} [MeasurableSpace Omega] (Q : Measure Omega)
    (M : EuclideanSCM kind dims) (K : ℝ≥0) (hK : VariablesBoundedAt M K)
    {r : ℕ} (sample : Fin r → Omega → Joint kind)
    (hsample : ∀ i, Measurable (sample i))
    (hlaw : ∀ i, Q.map (sample i) = observationalLaw M) :
    ∀ᵐ w ∂Q, ∀ i c, |(sample i w).ofLp c| ≤ estimationObservationRadius kind K := by
  apply ae_all_iff.mpr
  intro i
  have hS := (joint_coordinate_box_isCompact (kind := kind)
    (estimationObservationRadius kind K)).measurableSet
  have hmem : ∀ᵐ v ∂(observationalLaw M),
      v ∈ {v : Joint kind | ∀ c, |v.ofLp c| ≤ (estimationObservationRadius kind K : ℝ)} := by
    letI := observationalLaw_probability M
    apply (ae_mem_iff_measure_eq hS.nullMeasurableSet).mpr
    simpa only [measure_univ] using observationalLaw_estimationObservationBox M K hK
  rw [← hlaw i] at hmem
  exact (ae_map_iff (hsample i).aemeasurable hS).mp hmem

-- @node: restricted_ncm_sinkhorn_constraint_failure_le
/-- With [positive observed sample size](hyp:hr), [positive simulation size](hyp:hm),
and [output and Lipschitz bounds](hyp:K,L), assume [the reference model's variables
satisfy the output bound](hyp:hK), [observations are measurable](hyp:hsample) and
[have the reference observational law](hyp:hlaw), [the simulation tolerance](hyp:ha)
and [observation tolerance](hyp:ht) are nonnegative, and [regularization is positive](hyp:hlam).
Given [bounds on simulation and observation failure measures](hyp:failureSim,failureObs),
if [the uniform simulation Wasserstein error exceeds its tolerance only within
the simulation failure bound](hyp:hsim) and [the observed Wasserstein error
exceeds its tolerance only within the observation failure bound](hyp:hobs), then
[the measure of failure, for any restricted candidate, of either comparison
between population Wasserstein distance and empirical Sinkhorn divergence is
at most the sum of the two failure bounds, using slack equal to both tolerances
plus twice regularization times one plus the log of the product of sample sizes](goal). -/
lemma restricted_ncm_sinkhorn_constraint_failure_le
    {Omega : Type*} [MeasurableSpace Omega] (Q : Measure Omega)
    {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
    (M : EuclideanSCM kind dims) (K L : ℝ≥0) (hK : VariablesBoundedAt M K)
    {counts : Fin b → ℕ} (F0 : StructuralClass kind dims dag C)
    (F1 : GeneratorClass dims counts)
    (sample : Fin r → Omega → Joint kind)
    (hsample : ∀ i, Measurable (sample i))
    (hlaw : ∀ i, Q.map (sample i) = observationalLaw M)
    (draws : Fin m → Omega → SimulationInput kind counts)
    (a t lam : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) (hlam : 0 < lam)
    (failureSim failureObs : ℝ≥0∞)
    (hsim : Q {w | ∃ R : NCMIn kind dims dag G C counts F0 F1,
      restrictedCandidate K L R ∧
      ¬ wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
        (empiricalMeasure (fun i => ncmEval R (draws i w))) ≤ ENNReal.ofReal a} ≤ failureSim)
    (hobs : Q {w | ¬ wasserstein1 (observationalLaw M)
      (empiricalMeasure (fun i => sample i w)) ≤ ENNReal.ofReal t} ≤ failureObs) :
    Q {w | ∃ R : NCMIn kind dims dag G C counts F0 F1,
      restrictedCandidate K L R ∧
      let e := sinkhornDivergence lam (fun i => jointVector (ncmEval R (draws i w)))
        (fun i => jointVector (sample i w)) (uniformWeights m) (uniformWeights r)
      let slack := a + t + 2 * (Real.log (r * m : ℕ) + 1) * lam
      ¬ (wasserstein1 (observationalLaw R.canonical.toEuclideanSCM) (observationalLaw M) ≤
        ENNReal.ofReal (e + slack) ∧ ENNReal.ofReal (e - slack) ≤
          wasserstein1 (observationalLaw R.canonical.toEuclideanSCM) (observationalLaw M))} ≤
      failureSim + failureObs := by
  apply ncm_sinkhorn_constraint_failure_le Q hr hm M F0 F1 K L sample draws
    {v | ∀ c, |v.ofLp c| ≤ estimationObservationRadius kind K}
    (joint_coordinate_box_isCompact _) (fun R hR =>
      restrictedCandidate_observationalLaw_box K L R hR)
    (observationalLaw_estimationObservationBox M K hK) ?_
    a t lam ha ht hlam failureSim failureObs hsim hobs
  filter_upwards [observationalSample_ae_estimationObservationBox Q M K hK sample hsample hlaw]
    with w hw
  refine ⟨?_, hw⟩
  intro R hR i
  rintro ⟨j,k⟩
  exact restrictedCandidate_ncmEval_coordinate_bound K L R hR (draws i w) j k

end
end Papers.TbsNeuralCausalPi
