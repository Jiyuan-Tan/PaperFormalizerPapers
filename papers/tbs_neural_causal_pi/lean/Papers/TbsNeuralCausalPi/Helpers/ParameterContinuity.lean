module
public import Papers.TbsNeuralCausalPi.Helpers.ParameterTransport
public import Papers.TbsNeuralCausalPi.Helpers.ObjectiveTransport
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalConditionalPropensity
/-! # Continuity of population intervention laws and objectives

The clipped representatives have a common global Lipschitz bound. The causal
transport estimate therefore turns parameter convergence into a uniform bound
on bounded interventions, and intrinsic objective integrability passes this
bound to the actual iterated expectations.
-/
public section
namespace Papers.TbsNeuralCausalPi
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)} {K L : ℝ≥0}

/-- [A canonical causal model satisfies the categorical Gumbel-max sampling
assumption, including conditional category probabilities and boundary weights](goal). -/
-- @node: canonical_categoricalGumbelArgmax
lemma canonical_categoricalGumbelArgmax (M : CanonicalSCM kind dims dag G C) :
    CategoricalGumbelArgmax M.toEuclideanSCM M.f := by
  have hsum (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
      (x : Input kind dims dag C i) (hx : x ∈ M.domain i) :
      ∑ j, (M.f i x).ofLp j = 1 := by
    have hs := (M.simplex i k hi x hx.1).2
    exact (Equiv.sum_comp (finCongr (congrArg outputDim hi).symm) _).symm.trans hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i k hi x hx
    refine ⟨?_, by rw [hsum i k hi x hx]; exact zero_lt_one⟩
    intro j
    have hs := (M.simplex i k hi x hx.1).1
    obtain ⟨l, rfl⟩ := (finCongr (congrArg outputDim hi).symm).surjective j
    exact hs l
  · intro i k hi j
    have h := canonical_propensity_conditional_probability M i k hi j
    have he : (fun u => (M.f i (structuralInputRV M.toEuclideanSCM i u)).ofLp
        (Fin.cast (congrArg outputDim hi).symm j) /
          ∑ l, (M.f i (structuralInputRV M.toEuclideanSCM i u)).ofLp l) =
        (fun u => (M.f i (structuralInputRV M.toEuclideanSCM i u)).ofLp
          (Fin.cast (congrArg outputDim hi).symm j)) := by
      funext u
      rw [hsum i k hi _ (structuralInputRV_mem_domain M.toEuclideanSCM i u), div_one]
    rw [he]
    exact h
  · intro i k hi x hx g
    rw [canonicalMechanism_categoricalLabel_eq M i k hi]
    rfl
  · intro i k hi
    exact canonical_categorical_noise_law M i k hi

/-- If [the bounding radius is positive](hyp:hK) and [every categorical node's
number of categories is at most that radius](hyp:hlabels), [the clipped population
model has domain-Lipschitz mechanisms, independent latent blocks, a latent Gumbel
decomposition, categorical Gumbel-max sampling, Lipschitz continuous mechanisms
and categorical propensities, and almost surely bounded observed and non-Gumbel
latent coordinates](goal). -/
-- @node: boxTruncated_ofParam_regular_atoms
lemma boxTruncated_ofParam_regular_atoms
    (base : CanonicalSCM kind dims dag G C)
    (p : PopulationParam kind dims dag C K L) (hK : 0 < K)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K) :
    let N := boxTruncatedSCM (ofParam base p.parameter) K hlabels
    N ∈ canonicalClass (domainLipClass N L) ∧
      LatentBlocksIndependent N.toEuclideanSCM ∧
      LatentGumbelDecomposition N.toEuclideanSCM ∧
      CategoricalGumbelArgmax N.toEuclideanSCM N.f ∧
      ContinuousMechanismsLipschitz N.toEuclideanSCM L ∧
      CategoricalPropensityLipschitz N.toEuclideanSCM N.f L ∧
      VariablesBoundedAt N.toEuclideanSCM K := by
  let N := boxTruncatedSCM (ofParam base p.parameter) K hlabels
  have hLip : ∀ i, LipschitzOnWith L (N.f i) (N.domain i) :=
    fun i => (boxTruncated_ofParam_lipschitz base p hlabels i).lipschitzOnWith
  refine ⟨hLip, canonical_latent_blocks_independent N, ?_,
    canonical_categoricalGumbelArgmax N,
    canonical_continuousMechanismsLipschitz_of_structural N L hLip,
    canonical_categoricalPropensityLipschitz_of_structural N L hLip, ?_⟩
  · constructor
    · ext j
      cases j <;> simp
    · apply Set.disjoint_left.mpr
      rintro x ⟨a, rfl⟩ ⟨b, h⟩
      cases h
  · have hb := ofParam_variablesBoundedAt base p hK hlabels
    have he := boxTruncatedSCM_observational_eval_eq (ofParam base p.parameter)
      K K hlabels le_rfl hb
    refine ⟨hb.1, ?_⟩
    filter_upwards [hb.2, he] with u hu heq
    exact ⟨by simpa only [nodeCoordinate, ← heq.1] using hu.1, hu.2⟩

/-- If [the bounding radius is positive](hyp:hK) and [every categorical node's
number of categories is at most that radius](hyp:hlabels), [there is a positive
constant, uniform over population parameter pairs and interventions whose
assigned coordinates are bounded by the radius, that bounds the Wasserstein
distance between their intervention laws by the constant times their parameter
distance](goal). -/
-- @node: populationParam_interventional_wasserstein_bound
lemma populationParam_interventional_wasserstein_bound
    (base : CanonicalSCM kind dims dag G C) (hK : 0 < K)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K) :
    ∃ Q : ℝ≥0, 0 < Q ∧ ∀ p q : PopulationParam kind dims dag C K L,
      ∀ t : LawIntervention kind,
      (∀ i v, t.val i = some v → ∀ j, |v.ofLp j| ≤ K) →
      wasserstein1 (interventionalLaw (ofParam base p.parameter).toEuclideanSCM t)
        (interventionalLaw (ofParam base q.parameter).toEuclideanSCM t) ≤
          ENNReal.ofReal ((Q : ℝ) * paramDist p q) := by
  obtain ⟨Q, hQ, htransport⟩ := bounded_interventional_wasserstein_bound
    (kind := kind) (dims := dims) (dag := dag) (G := G) (C := C) L K hK
  refine ⟨Q, hQ, ?_⟩
  intro p q t ht
  obtain ⟨hc, hi, hd, hg, hco, hp, hb⟩ :=
    boxTruncated_ofParam_regular_atoms base p hK hlabels
  have hqb := (boxTruncated_ofParam_regular_atoms base q hK hlabels).2.2.2.2.2.2
  have hw := htransport
    (boxTruncatedSCM (ofParam base p.parameter) K hlabels)
    (boxTruncatedSCM (ofParam base q.parameter) K hlabels)
    hlabels hc hi hd hg hco hp hb hqb
    (fun i d hi x _ => boxTruncated_ofParam_continuous_output_bound base p hlabels i d hi x)
    (fun i d hi x _ => boxTruncated_ofParam_continuous_output_bound base q hlabels i d hi x) t ht
  rw [boxTruncated_ofParam_interventionalLaw_eq base p hK hlabels t ht,
    boxTruncated_ofParam_interventionalLaw_eq base q hK hlabels t ht] at hw
  apply hw.trans
  have he := boxTruncated_ofParam_transport_error_le_paramDist base p q hlabels
    (fun i => (boxTruncatedSCM (ofParam base p.parameter) K hlabels).domain i
      (some (-(K : ℝ), K)))
  have hm := mul_le_mul' (le_refl (Q : ℝ≥0∞)) he
  simpa only [ENNReal.ofReal_mul Q.coe_nonneg, ENNReal.ofReal_coe_nnreal] using hm

/-- If [the bounding radius is positive](hyp:hK), [every categorical node's
number of categories is at most that radius](hyp:hlabels), [the sequence converges
to the target in parameter distance](hyp:h), and [the intervention's assigned
coordinates are bounded by the radius](hyp:ht), [the Wasserstein distance between
the sequence's intervention laws and the target intervention law tends to zero](goal). -/
-- @node: populationParam_interventional_wasserstein_tendsto
lemma populationParam_interventional_wasserstein_tendsto
    (base : CanonicalSCM kind dims dag G C) (hK : 0 < K)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (p : ℕ → PopulationParam kind dims dag C K L)
    (q : PopulationParam kind dims dag C K L)
    (h : Tendsto (fun r => paramDist (p r) q) atTop (𝓝 0))
    (t : LawIntervention kind)
    (ht : ∀ i v, t.val i = some v → ∀ j, |v.ofLp j| ≤ K) :
    Tendsto (fun r => wasserstein1
      (interventionalLaw (ofParam base (p r).parameter).toEuclideanSCM t)
      (interventionalLaw (ofParam base q.parameter).toEuclideanSCM t))
      atTop (𝓝 0) := by
  obtain ⟨Q, hQ, hW⟩ := populationParam_interventional_wasserstein_bound base hK hlabels
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.tendsto_ofReal (h.const_mul (Q : ℝ)))
    (fun _ => bot_le) (fun r => hW (p r) q t ht)

/-- Suppose [the bounding radius is positive](hyp:hK), [every categorical node's
number of categories is at most that radius](hyp:hlabels), [the parameters
converge to the target in parameter distance](hyp:h), and [the intervention domain
has full probability and bounds both category counts and assigned intervention
coordinates by that radius](hyp:hdomain).
If [the outcome criterion is Lipschitz](hyp:hF), [the target objective is
defined](hyp:hq), and [the sequence's objectives are eventually defined](hyp:hp),
[the intervention-averaged objectives converge to the target objective](goal). -/
-- @node: populationParam_objectiveIntegral_tendsto
lemma populationParam_objectiveIntegral_tendsto
    (base : CanonicalSCM kind dims dag G C) (hK : 0 < K)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (p : ℕ → PopulationParam kind dims dag C K L)
    (q : PopulationParam kind dims dag C K L)
    (h : Tendsto (fun r => paramDist (p r) q) atTop (𝓝 0))
    {I : Type*} [MeasurableSpace I] (t : I → LawIntervention kind)
    (muT : Measure I) [IsProbabilityMeasure muT] (domain : Set I)
    (hdomain : populationObjectiveDomain K domain t muT)
    (F : Joint kind → ℝ) {LF : ℝ≥0} (hF : LipschitzWith LF F)
    (hq : objectiveDefined (ofParam base q.parameter).toEuclideanSCM t muT F)
    (hp : ∀ᶠ r in atTop,
      objectiveDefined (ofParam base (p r).parameter).toEuclideanSCM t muT F) :
    Tendsto (fun r => objectiveIntegral (ofParam base (p r).parameter).toEuclideanSCM t muT F)
      atTop (𝓝 (objectiveIntegral (ofParam base q.parameter).toEuclideanSCM t muT F)) := by
  obtain ⟨Q, hQ, hW⟩ := populationParam_interventional_wasserstein_bound base hK hlabels
  apply objectiveIntegral_tendsto_of_interventional_transport
    (ofParam base q.parameter).toEuclideanSCM
    (fun r => (ofParam base (p r).parameter).toEuclideanSCM)
    t muT F hF hq hp (fun r => (Q : ℝ) * paramDist (p r) q)
    (by simpa using h.const_mul (Q : ℝ))
    (Eventually.of_forall (fun r => mul_nonneg Q.coe_nonneg (paramDist_nonneg (p r) q)))
  apply Eventually.of_forall
  intro r
  have hmem : ∀ᵐ s ∂muT, s ∈ domain := ae_iff.mpr hdomain.2.2
  filter_upwards [hmem] with s hs
  exact hW (p r) q (t s) (hdomain.2.1 s hs)

end Papers.TbsNeuralCausalPi
