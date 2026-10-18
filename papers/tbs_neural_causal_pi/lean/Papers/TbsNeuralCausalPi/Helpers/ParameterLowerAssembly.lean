module
public import Papers.TbsNeuralCausalPi.Helpers.ParameterDiscrepancy
public import Papers.TbsNeuralCausalPi.Helpers.EstimationSequential
/-! # Lower bounds on shrinking neural parameter sublevels

Compactness is applied to positive-index neural tuples. The intrinsic objective
hypothesis is used only on their closure, including the extracted limit.
-/
public section
namespace Papers.TbsNeuralCausalPi
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)} {K L : ℝ≥0}

-- @node: populationRepresentation_interventionalLaw_eq
/-- If [a population parameter agrees with a neural candidate on actual cube
inputs and represents its latent block laws](hyp:hp), [every categorical
label count is at most K](hyp:hlabels), and [every imposed intervention
coordinate has absolute value at most K](hyp:ht), [the candidate and the
parameter's ambient representative have the same interventional law](goal). -/
lemma populationRepresentation_interventionalLaw_eq
    (base : CanonicalSCM kind dims dag G C)
    {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    {F1 : GeneratorClass dims counts}
    (p : PopulationParam kind dims dag C K L)
    (R : NCMIn kind dims dag G C counts F0 F1)
    (hp : populationRepresentation p R)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (t : LawIntervention kind)
    (ht : ∀ i v, t.val i = some v → ∀ j, |v.ofLp j| ≤ K) :
    interventionalLaw R.canonical.toEuclideanSCM t =
      interventionalLaw (ofParam base p.parameter).toEuclideanSCM t := by
  let N := ofParam base p.parameter
  have hlaw : R.canonical.latentLaw = N.latentLaw := by
    unfold CanonicalSCM.latentLaw
    simp_rw [hp.2]
    rfl
  unfold interventionalLaw
  change R.canonical.latentLaw.map _ = N.latentLaw.map _
  rw [hlaw]
  apply Measure.map_congr
  filter_upwards [ofParam_latent_coordinates_bounded base p.parameter] with u hu
  apply canonical_evalSteps_eq_of_weights_eq R.canonical N t.val u (n*n+n)
  intro r hr i hi
  have hx : structuralInput N.toEuclideanSCM i
      (evalSteps N.toEuclideanSCM t.val u r) u ∈ inputCube K i := by
    intro c
    cases c with
    | inl v =>
      exact ofParam_evalSteps_coordinate_bounded base p.parameter t.val u
        hlabels ht r v.1.val v.2
    | inr v => exact hu v.1.val v.2
  change R.canonical.f i _ = paramFunction p.parameter i _
  simp only [paramFunction, dif_pos hx]
  exact hp.1 i ⟨_, hx⟩
    (evalSteps_structuralInput_mem_domain N.toEuclideanSCM t.val t.property u i r hi)

-- @node: populationRepresentation_objectiveIntegral_eq
/-- If [a population parameter represents a neural candidate](hyp:hp),
[categorical label counts and intervention coordinates are bounded by K
on an intervention domain of full probability](hyp:hdomain),
[the candidate's iterated objective is well defined](hyp:hR), and [the
parameter representative's iterated objective is well defined](hyp:hdefined),
[their real objective
integrals are equal](goal). -/
lemma populationRepresentation_objectiveIntegral_eq
    (base : CanonicalSCM kind dims dag G C)
    {counts : Fin b → ℕ} {F0 : StructuralClass kind dims dag C}
    {F1 : GeneratorClass dims counts}
    (p : PopulationParam kind dims dag C K L)
    (R : NCMIn kind dims dag G C counts F0 F1)
    (hp : populationRepresentation p R)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (domain : Set I)
    (hdomain : populationObjectiveDomain K domain t muT)
    (F : Joint kind → ℝ)
    (hR : objectiveDefined R.canonical.toEuclideanSCM t muT F)
    (hdefined : objectiveDefined (ofParam base p.parameter).toEuclideanSCM t muT F) :
    objectiveIntegral R.canonical.toEuclideanSCM t muT F =
      objectiveIntegral (ofParam base p.parameter).toEuclideanSCM t muT F := by
  exact consistencyObjective_eq_of_cube_agreement base R.canonical p t muT F
    domain hdomain hp.1 hp.2 hR hdefined

-- @node: parameterObjectivesDefined_eventually_lower
/-- Suppose [K is strictly positive](hyp:hK), [the base model's variables
are bounded by K](hyp:hbase), [categorical label counts and intervention
coordinates are bounded by K on an intervention domain of full
probability](hyp:hdomain), and [the objective function is Lipschitz](hyp:hF).
If [objectives are well defined on the closure of the parameter sets](hyp:hdefined)
and [objectives are well defined on all feasible population models](hyp:hpopulation), [the observational
tolerances tend to zero](hyp:hbeta), and [c is strictly below the population
lower bound](hyp:hc), [eventually every parameter in the corresponding set
whose real observational Wasserstein discrepancy is within its tolerance
has objective strictly greater than c](goal). -/
lemma parameterObjectivesDefined_eventually_lower
    (base : CanonicalSCM kind dims dag G C) (hK : 0 < K)
    (hbase : VariablesBoundedAt base.toEuclideanSCM K)
    (Theta : ℕ → Set (ProofPopulationParam kind dims dag C K L))
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (domain : Set I)
    (hdomain : populationObjectiveDomain K domain t muT)
    (F : Joint kind → ℝ) {LF : ℝ≥0} (hF : LipschitzWith LF F)
    (hdefined : parameterObjectivesDefined base Theta t muT F)
    (hpopulation : populationObjectivesDefined base K L t muT F)
    (beta : ℕ → ℝ) (hbeta : Tendsto beta atTop (𝓝 0))
    {c : ℝ} (hc : (c : EReal) < populationLowerBound base K L t muT F hpopulation) :
    ∀ᶠ r in atTop, ∀ p : PopulationParam kind dims dag C K L,
      p.parameter ∈ Theta r →
      (wasserstein1 (observationalLaw (ofParam base p.parameter).toEuclideanSCM)
        (observationalLaw base.toEuclideanSCM)).toReal ≤ beta r →
      c < objectiveIntegral (ofParam base p.parameter).toEuclideanSCM t muT F := by
  classical
  by_contra h
  have hbad : ∃ᶠ r in atTop, ∃ p : PopulationParam kind dims dag C K L,
      p.parameter ∈ Theta r ∧
      (wasserstein1 (observationalLaw (ofParam base p.parameter).toEuclideanSCM)
        (observationalLaw base.toEuclideanSCM)).toReal ≤ beta r ∧
      objectiveIntegral (ofParam base p.parameter).toEuclideanSCM t muT F ≤ c := by
    have hf : ∃ᶠ r in atTop, ¬ (∀ p : PopulationParam kind dims dag C K L,
        p.parameter ∈ Theta r →
        (wasserstein1 (observationalLaw (ofParam base p.parameter).toEuclideanSCM)
          (observationalLaw base.toEuclideanSCM)).toReal ≤ beta r →
        c < objectiveIntegral (ofParam base p.parameter).toEuclideanSCM t muT F) := by
      simpa only [Filter.Frequently, not_not] using h
    exact hf.mono (fun _ hr => by
      simpa only [not_forall, Classical.not_imp, not_lt, exists_prop, and_assoc] using hr)
  obtain ⟨s, hs, hbad⟩ := extraction_of_frequently_atTop hbad
  choose p hp hpg hpf using hbad
  obtain ⟨q, phi, hphi, hdist⟩ := estimation_population_paramDist_subsequence K L p
  have hindices : Tendsto (fun r => s (phi r)) atTop atTop :=
    hs.tendsto_atTop.comp hphi.tendsto_atTop
  have hmem : ∀ r, (p (phi r)).parameter ∈ Theta (s (phi r)) := fun r => hp (phi r)
  have hclosure := proofConsistencyParamClosure_mem_of_paramDist_tendsto
    Theta (fun r => p (phi r)) q (fun r => s (phi r)) hindices hmem hdist
  have hobj := parameterObjectivesDefined_objectiveIntegral_tendsto
    base hK Theta t muT domain hdomain F hF hdefined
    (fun r => p (phi r)) q (fun r => s (phi r)) hindices hmem hdist
  have hobs := populationParam_observational_discrepancy_tendsto
    base hK hdomain.1 hbase (fun r => p (phi r)) q hdist
  have hzero : Tendsto (fun r => (wasserstein1
      (observationalLaw (ofParam base (p (phi r)).parameter).toEuclideanSCM)
      (observationalLaw base.toEuclideanSCM)).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun r => hpg (phi r))
      (hbeta.comp hindices)
  have hg : (wasserstein1 (observationalLaw (ofParam base q.parameter).toEuclideanSCM)
      (observationalLaw base.toEuclideanSCM)).toReal = 0 := tendsto_nhds_unique hobs hzero
  have hW : wasserstein1 (observationalLaw (ofParam base q.parameter).toEuclideanSCM)
      (observationalLaw base.toEuclideanSCM) = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp hg).resolve_right
      (populationParam_observational_discrepancy_ne_top base hK hdomain.1 hbase q)
  have hlower := populationLowerBound_le_cube_objective base q hK hdomain.1
    t muT F domain hdomain hpopulation (hdefined q.parameter hclosure) hW
  have hle : objectiveIntegral (ofParam base q.parameter).toEuclideanSCM t muT F ≤ c :=
    le_of_tendsto' hobj (fun r => hpf (phi r))
  exact (not_lt_of_ge (hlower.trans (EReal.coe_le_coe_iff.mpr hle))) hc

-- @node: restrictedEmpiricalPIValue_liminf_ge_of_cube_representatives
/-- Suppose [K is strictly positive](hyp:hK), [the base model's variables
are bounded by K](hyp:hbase), [categorical label counts and intervention
coordinates are bounded by K on an intervention domain of full
probability](hyp:hdomain), and [the objective function is Lipschitz](hyp:hF).
Assume [objectives are well defined on the closure of the neural parameter
sets](hyp:hdefined), [objectives are well defined on all feasible population
models](hyp:hpopulation), and [objectives are well defined for every
restricted neural candidate at each index](hyp:hempirical).
For [observational samples of size r at index r](hyp:sample) and
[simulation draws of size m at each index](hyp:draws), if [the observational
tolerances tend to zero](hyp:hbeta), [these tolerances are nonnegative](hyp:hbetaNonneg),
[every restricted neural candidate has a population cube representative](hyp:hrepresentatives),
and [eventually every restricted candidate satisfying the empirical Sinkhorn
constraint has population observational Wasserstein discrepancy bounded by
the corresponding tolerance](hyp:hcontrol), [the population lower bound is
at most the lower limit of the restricted empirical partial-identification
values](goal). -/
lemma restrictedEmpiricalPIValue_liminf_ge_of_cube_representatives
    (base : CanonicalSCM kind dims dag G C) (hK : 0 < K)
    (hbase : VariablesBoundedAt base.toEuclideanSCM K)
    {counts : Fin b → ℕ}
    (F0 : ℕ → StructuralClass kind dims dag C) (F1 : ℕ → GeneratorClass dims counts)
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (domain : Set I)
    (hdomain : populationObjectiveDomain K domain t muT)
    (F : Joint kind → ℝ) {LF : ℝ≥0} (hF : LipschitzWith LF F)
    (hdefined : parameterObjectivesDefined base (consistencyNeuralParameters (G := G) K L F0 F1)
      t muT F)
    (hpopulation : populationObjectivesDefined base K L t muT F)
    (hempirical : ∀ r, empiricalObjectivesDefined (G := G) (F0 r) (F1 r)
      (restrictedCandidate K L) t muT F)
    (m : ℕ → ℕ) (sample : ∀ r, Fin r → Joint kind)
    (draws : ∀ r, Fin (m r) → SimulationInput kind counts)
    (lam alpha beta : ℕ → ℝ) (hbeta : Tendsto beta atTop (𝓝 0))
    (hbetaNonneg : ∀ r, 0 ≤ beta r)
    (hrepresentatives : ∀ r, ∀ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
      restrictedCandidate K L R → ∃ p : PopulationParam kind dims dag C K L,
        populationRepresentation p R)
    (hcontrol : ∀ᶠ r in atTop,
      ∀ R : NCMIn kind dims dag G C counts (F0 r) (F1 r),
      restrictedCandidate K L R →
      sinkhornDivergence (lam r) (fun i => jointVector (ncmEval R (draws r i)))
        (fun i => jointVector (sample r i)) (uniformWeights (m r)) (uniformWeights r) ≤
          alpha r →
      wasserstein1 (observationalLaw R.canonical.toEuclideanSCM)
        (observationalLaw base.toEuclideanSCM) ≤ ENNReal.ofReal (beta r)) :
    populationLowerBound base K L t muT F hpopulation ≤
      liminf (fun r => restrictedEmpiricalPIValue (G := G) (F0 r) (F1 r)
        K L t muT F (sample r) (draws r) (lam r) (alpha r) (hempirical r)) atTop := by
  apply (le_liminf_iff').mpr
  intro y hy
  induction y using EReal.rec with
  | bot => exact Eventually.of_forall (fun _ => bot_le)
  | top => exact False.elim (not_lt_of_ge le_top hy)
  | coe c =>
    filter_upwards [parameterObjectivesDefined_eventually_lower base hK hbase
      (consistencyNeuralParameters (G := G) K L F0 F1) t muT domain hdomain F hF
      hdefined hpopulation beta hbeta hy, hcontrol, eventually_ge_atTop 1]
      with r hr hctrl hpos
    unfold restrictedEmpiricalPIValue empiricalPIValueOn
    apply le_iInf
    intro R
    apply le_iInf
    intro hR
    apply le_iInf
    intro hfeas
    obtain ⟨p, hp⟩ := hrepresentatives r R hR
    have hmem : p.parameter ∈ consistencyNeuralParameters (G := G) K L F0 F1 r := ⟨R, hR, hp⟩
    have hpdefined := hdefined p.parameter
      (proofConsistencyParamClosure_mem_of_mem _ p hpos hmem)
    have hlaw := populationRepresentation_interventionalLaw_eq base p R hp hdomain.1
      (noIntervention kind) (by simp [noIntervention])
    have hb := hctrl R hR hfeas
    change wasserstein1 (interventionalLaw R.canonical.toEuclideanSCM (noIntervention kind))
      (observationalLaw base.toEuclideanSCM) ≤ _ at hb
    rw [hlaw] at hb
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal (hbetaNonneg r)] at hreal
    have hlt := hr p hmem hreal
    have hobj := populationRepresentation_objectiveIntegral_eq base p R hp
      t muT domain hdomain F (hempirical r R hR) hpdefined
    change (c : EReal) ≤ (objectiveIntegral R.canonical.toEuclideanSCM t muT F : EReal)
    rw [hobj]
    exact EReal.coe_le_coe_iff.mpr hlt.le

end Papers.TbsNeuralCausalPi
