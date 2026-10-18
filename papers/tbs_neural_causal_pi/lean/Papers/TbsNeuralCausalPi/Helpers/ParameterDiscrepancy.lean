module
public import Papers.TbsNeuralCausalPi.Helpers.ParameterContinuity
public import Papers.TbsNeuralCausalPi.Helpers.EstimationSamplingSupport
/-! # Observational discrepancy on the compact population parameter space

The triangle inequality on a common compact carrier controls the real-valued
observational discrepancy. Positive-index limits also belong to precisely the
parameter closure on which the intrinsic objective domain is supplied.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

-- @node: wasserstein1_ne_top_compact_mass
/-- If [a common set is compact](hyp:hS), [the first probability distribution
assigns it probability one](hyp:hm), and [the second probability distribution
assigns it probability one](hyp:hn),
[their Wasserstein distance is finite](goal). -/
lemma wasserstein1_ne_top_compact_mass
    {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S : Set X) (hS : IsCompact S) (hm : mu S = 1) (hn : nu S = 1) :
    wasserstein1 mu nu ≠ ⊤ := by
  letI := isCompact_iff_compactSpace.mp hS
  have hmP := (Toolkit.Foundations.MeasureTheory.probability_comap_subtype
    mu S hS.measurableSet hm).1
  have hnP := (Toolkit.Foundations.MeasureTheory.probability_comap_subtype
    nu S hS.measurableSet hn).1
  rw [wasserstein1_eq_toolkit,
    Toolkit.Foundations.MeasureTheory.wasserstein1_subtype_comap
      mu nu S hS.measurableSet hm hn, ← wasserstein1_eq_toolkit]
  exact wasserstein1_ne_top_compact ⟨_, hmP⟩ ⟨_, hnP⟩

/-- If [a common set is compact](hyp:hS), [the first probability distribution
assigns it probability one](hyp:hm), [the second assigns it probability one](hyp:hn),
and [the reference distribution assigns it probability one](hyp:hr),
[the absolute difference between the first two distributions'
real-valued Wasserstein distances to the reference is at most their real-valued
Wasserstein distance to each other](goal). -/
-- @node: wasserstein1_toReal_abs_sub_le_compact_mass
lemma wasserstein1_toReal_abs_sub_le_compact_mass
    {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    (mu nu rho : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsProbabilityMeasure rho] (S : Set X) (hS : IsCompact S)
    (hm : mu S = 1) (hn : nu S = 1) (hr : rho S = 1) :
    |(wasserstein1 mu rho).toReal - (wasserstein1 nu rho).toReal| ≤
      (wasserstein1 mu nu).toReal := by
  have hmn := wasserstein1_ne_top_compact_mass mu nu S hS hm hn
  have hmr := wasserstein1_ne_top_compact_mass mu rho S hS hm hr
  have hnr := wasserstein1_ne_top_compact_mass nu rho S hS hn hr
  have hsym : wasserstein1 nu mu = wasserstein1 mu nu :=
    wasserstein1_symm ⟨nu, inferInstance⟩ ⟨mu, inferInstance⟩
  have hnm : wasserstein1 nu mu ≠ ⊤ := by rwa [hsym]
  have h₁ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hmn, hnr⟩)
    (wasserstein1_triangle_compact_mass mu nu rho S hS hm hn hr)
  have h₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hnm, hmr⟩)
    (wasserstein1_triangle_compact_mass nu mu rho S hS hn hm hr)
  rw [ENNReal.toReal_add hmn hnr] at h₁
  rw [ENNReal.toReal_add hnm hmr, hsym] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)} {K L : ℝ≥0}

-- @node: populationParam_observational_discrepancy_ne_top
/-- If [the bounding radius is positive](hyp:hK), [every categorical node's
number of categories is at most that radius](hyp:hlabels), and [the base model's
observed and latent variables are bounded by that radius](hyp:hbase), [the
Wasserstein distance between any population parameter model's observational law
and the base model's observational law is finite](goal). -/
lemma populationParam_observational_discrepancy_ne_top
    (base : CanonicalSCM kind dims dag G C) (hK : 0 < K)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (hbase : VariablesBoundedAt base.toEuclideanSCM K)
    (p : PopulationParam kind dims dag C K L) :
    wasserstein1 (observationalLaw (ofParam base p.parameter).toEuclideanSCM)
      (observationalLaw base.toEuclideanSCM) ≠ ⊤ := by
  letI := observationalLaw_probability (ofParam base p.parameter).toEuclideanSCM
  letI := observationalLaw_probability base.toEuclideanSCM
  exact wasserstein1_ne_top_compact_mass _ _ {v | ∀ c, |v.ofLp c| ≤ (K : ℝ)}
    (joint_coordinate_box_isCompact K)
    (observationalLaw_bounded_coordinates _ K (ofParam_variablesBoundedAt base p hK hlabels))
    (observationalLaw_bounded_coordinates _ K hbase)

/-- If [the bounding radius is positive](hyp:hK), [every categorical node's
number of categories is at most that radius](hyp:hlabels), and [the base model's
observed and latent variables are bounded by that radius](hyp:hbase), [there is
a positive constant such that, for every pair of population parameters, the
absolute difference between their real-valued observational Wasserstein
discrepancies from the base law is at most that constant times their parameter
distance](goal). -/
-- @node: populationParam_observational_discrepancy_bound
lemma populationParam_observational_discrepancy_bound
    (base : CanonicalSCM kind dims dag G C) (hK : 0 < K)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (hbase : VariablesBoundedAt base.toEuclideanSCM K) :
    ∃ Q : ℝ≥0, 0 < Q ∧ ∀ p q : PopulationParam kind dims dag C K L,
      |(wasserstein1 (observationalLaw (ofParam base p.parameter).toEuclideanSCM)
          (observationalLaw base.toEuclideanSCM)).toReal -
        (wasserstein1 (observationalLaw (ofParam base q.parameter).toEuclideanSCM)
          (observationalLaw base.toEuclideanSCM)).toReal| ≤ (Q : ℝ) * paramDist p q := by
  obtain ⟨Q, hQ, hW⟩ := populationParam_interventional_wasserstein_bound base hK hlabels
  refine ⟨Q, hQ, ?_⟩
  intro p q
  letI := observationalLaw_probability (ofParam base p.parameter).toEuclideanSCM
  letI := observationalLaw_probability (ofParam base q.parameter).toEuclideanSCM
  letI := observationalLaw_probability base.toEuclideanSCM
  have h := wasserstein1_toReal_abs_sub_le_compact_mass
    (observationalLaw (ofParam base p.parameter).toEuclideanSCM)
    (observationalLaw (ofParam base q.parameter).toEuclideanSCM)
    (observationalLaw base.toEuclideanSCM) {v | ∀ c, |v.ofLp c| ≤ (K : ℝ)}
    (joint_coordinate_box_isCompact K)
    (observationalLaw_bounded_coordinates _ K (ofParam_variablesBoundedAt base p hK hlabels))
    (observationalLaw_bounded_coordinates _ K (ofParam_variablesBoundedAt base q hK hlabels))
    (observationalLaw_bounded_coordinates _ K hbase)
  apply h.trans
  have hb := hW p q (noIntervention kind) (by simp [noIntervention])
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [observationalLaw, ENNReal.toReal_ofReal
    (mul_nonneg Q.coe_nonneg (paramDist_nonneg p q))] using hr

-- @node: populationParam_observational_discrepancy_tendsto
/-- If [the bounding radius is positive](hyp:hK), [every categorical node's
number of categories is at most that radius](hyp:hlabels), [the base model's
observed and latent variables are bounded by that radius](hyp:hbase), and
[the parameters converge to a target in parameter distance](hyp:h), [their
real-valued observational Wasserstein discrepancies from the base law converge
to the target's discrepancy](goal). -/
lemma populationParam_observational_discrepancy_tendsto
    (base : CanonicalSCM kind dims dag G C) (hK : 0 < K)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (hbase : VariablesBoundedAt base.toEuclideanSCM K)
    (p : ℕ → PopulationParam kind dims dag C K L)
    (q : PopulationParam kind dims dag C K L)
    (h : Tendsto (fun r => paramDist (p r) q) atTop (𝓝 0)) :
    Tendsto (fun r => (wasserstein1
      (observationalLaw (ofParam base (p r).parameter).toEuclideanSCM)
      (observationalLaw base.toEuclideanSCM)).toReal) atTop
      (𝓝 (wasserstein1 (observationalLaw (ofParam base q.parameter).toEuclideanSCM)
        (observationalLaw base.toEuclideanSCM)).toReal) := by
  obtain ⟨Q, _, hQ⟩ := populationParam_observational_discrepancy_bound base hK hlabels hbase
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ => dist_nonneg)
    (fun r => by simpa only [Real.dist_eq] using hQ (p r) q)
    (by simpa using h.const_mul (Q : ℝ))

-- @node: paramDist_comm
/-- [The parameter distance between two population parameters is unchanged
when their order is reversed](goal). -/
lemma paramDist_comm (p q : PopulationParam kind dims dag C K L) :
    paramDist p q = paramDist q p := by
  unfold paramDist cubeParamDist
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [supDistOn, WithLp.ofLp_sub, norm_sub_rev]
  · apply Finset.sum_congr rfl
    intro j _
    rw [wasserstein1_symm (p.parameter.2 j) (q.parameter.2 j)]

-- @node: paramDist_self
/-- [The parameter distance from any population parameter to itself is zero](goal). -/
lemma paramDist_self (p : PopulationParam kind dims dag C K L) :
    paramDist p p = 0 := by
  letI (j : Fin b) := isCompact_iff_compactSpace.mp (boundedCube_isCompact (dims j) K)
  have hW (j : Fin b) : wasserstein1 (p.parameter.2 j : Measure (boundedCube (dims j) K))
      (p.parameter.2 j : Measure (boundedCube (dims j) K)) = 0 :=
    (wasserstein1_eq_zero_iff_compact _ _).mpr rfl
  simp only [paramDist, cubeParamDist, supDistOn, sub_self, WithLp.ofLp_zero,
    norm_zero, ENNReal.ofReal_zero, ENNReal.toReal_zero,
    Finset.sum_const_zero, hW, zero_add]
  simp

-- @node: proofConsistencyParamClosure_mem_of_mem
/-- If [an index is at least one](hyp:hr) and [a population parameter belongs to
the parameter class at that index](hyp:hp), [it belongs to the closure of the
positive-index parameter classes in parameter distance](goal). -/
lemma proofConsistencyParamClosure_mem_of_mem
    (Theta : ℕ → Set (ProofPopulationParam kind dims dag C K L))
    (p : PopulationParam kind dims dag C K L) {r : ℕ} (hr : 1 ≤ r)
    (hp : p.parameter ∈ Theta r) :
    p.parameter ∈ proofConsistencyParamClosure Theta := by
  intro eps heps
  refine ⟨r, hr, p.parameter, hp, ?_⟩
  change paramDist p p < eps
  rwa [paramDist_self]

/-- If [the class indices tend to infinity](hyp:hindices), [each parameter in
the sequence belongs to its indexed class](hyp:hp), and [the sequence converges
to a target in parameter distance](hyp:h), [the target belongs to the closure
of the positive-index parameter classes in parameter distance](goal). -/
-- @node: proofConsistencyParamClosure_mem_of_paramDist_tendsto
lemma proofConsistencyParamClosure_mem_of_paramDist_tendsto
    (Theta : ℕ → Set (ProofPopulationParam kind dims dag C K L))
    (p : ℕ → PopulationParam kind dims dag C K L)
    (q : PopulationParam kind dims dag C K L) (indices : ℕ → ℕ)
    (hindices : Tendsto indices atTop atTop)
    (hp : ∀ r, (p r).parameter ∈ Theta (indices r))
    (h : Tendsto (fun r => paramDist (p r) q) atTop (𝓝 0)) :
    q.parameter ∈ proofConsistencyParamClosure Theta := by
  intro eps heps
  obtain ⟨r, hpos, hsmall⟩ := ((hindices.eventually (eventually_ge_atTop 1)).and
    (h.eventually (gt_mem_nhds heps))).exists
  refine ⟨indices r, hpos, (p r).parameter, hp r, ?_⟩
  change paramDist q (p r) < eps
  rwa [paramDist_comm]

/-- Suppose [the bounding radius is positive](hyp:hK), [the intervention domain
has full probability and bounds both category counts and assigned intervention
coordinates by that radius](hyp:hdomain),
[the outcome criterion is Lipschitz](hyp:hF), and [objectives are defined throughout
the closure of the positive-index parameter classes](hyp:hdefined).
If [the class indices tend to infinity](hyp:hindices), [each parameter belongs to
its indexed class](hyp:hp), and [the sequence converges to a target in parameter
distance](hyp:h), [its intervention-averaged objectives converge to the target
objective](goal). -/
-- @node: parameterObjectivesDefined_objectiveIntegral_tendsto
lemma parameterObjectivesDefined_objectiveIntegral_tendsto
    (base : CanonicalSCM kind dims dag G C) (hK : 0 < K)
    (Theta : ℕ → Set (ProofPopulationParam kind dims dag C K L))
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (domain : Set I)
    (hdomain : populationObjectiveDomain K domain t muT)
    (F : Joint kind → ℝ) {LF : ℝ≥0} (hF : LipschitzWith LF F)
    (hdefined : parameterObjectivesDefined base Theta t muT F)
    (p : ℕ → PopulationParam kind dims dag C K L)
    (q : PopulationParam kind dims dag C K L) (indices : ℕ → ℕ)
    (hindices : Tendsto indices atTop atTop)
    (hp : ∀ r, (p r).parameter ∈ Theta (indices r))
    (h : Tendsto (fun r => paramDist (p r) q) atTop (𝓝 0)) :
    Tendsto (fun r => objectiveIntegral (ofParam base (p r).parameter).toEuclideanSCM
      t muT F) atTop
      (𝓝 (objectiveIntegral (ofParam base q.parameter).toEuclideanSCM t muT F)) := by
  apply populationParam_objectiveIntegral_tendsto base hK hdomain.1 p q h
    t muT domain hdomain F hF
  · exact hdefined q.parameter
      (proofConsistencyParamClosure_mem_of_paramDist_tendsto Theta p q indices hindices hp h)
  · filter_upwards [hindices.eventually (eventually_ge_atTop 1)] with r hr
    exact hdefined (p r).parameter
      (proofConsistencyParamClosure_mem_of_mem Theta (p r) hr (hp r))

end Papers.TbsNeuralCausalPi
