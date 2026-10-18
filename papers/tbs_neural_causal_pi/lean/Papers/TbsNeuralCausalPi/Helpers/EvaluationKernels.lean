module
public import Papers.TbsNeuralCausalPi.Helpers.EvaluationNoise
public import Papers.TbsNeuralCausalPi.Helpers.InterventionDomains
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationTransport
/-! # Canonical evaluation as a chain of independent-noise kernels

The kernel representation is exact for categorical as well as continuous
nodes. Empty topological slots use the identity kernel.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false
set_option linter.unusedVariables false

/-- For [a fixed private-input measure](hyp:rho) and [an update taking a state and a
private input to a new state](hyp:F) that [is measurable](hyp:hF), [the private-noise
update kernel](goal) assigns to each state the distribution of its update under that measure. -/
-- @node: privateNoiseUpdateKernel
def privateNoiseUpdateKernel
    {X Z Y : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
    (rho : Measure Z) [SFinite rho] (F : X × Z → Y) (hF : Measurable F) :
    Kernel X Y where
  toFun x := rho.map (fun z => F (x,z))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    change Measurable (fun x => (rho.map (fun z => F (x,z))) s)
    have he : (fun x => (rho.map (fun z => F (x,z))) s) =
        (fun x => rho (Prod.mk x ⁻¹' (F ⁻¹' s))) := by
      funext x
      exact Measure.map_apply (hF.comp measurable_prodMk_left) hs
    rw [he]
    exact measurable_measure_prodMk_left (hs.preimage hF)

-- @node: privateNoiseUpdateKernel_markov
/-- For [a private-input probability measure](hyp:rho) and [a state update](hyp:F)
that [is measurable](hyp:hF), [the private-noise update kernel assigns a probability
measure to every state](goal). -/
instance privateNoiseUpdateKernel_markov
    {X Z Y : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
    (rho : Measure Z) [IsProbabilityMeasure rho] (F : X × Z → Y) (hF : Measurable F) :
    IsMarkovKernel (privateNoiseUpdateKernel rho F hF) := by
  constructor
  intro x
  change IsProbabilityMeasure (rho.map (fun z => F (x,z)))
  exact Measure.isProbabilityMeasure_map (hF.comp measurable_prodMk_left).aemeasurable

/-- If [the state-and-private-input update is measurable](hyp:hF), then
[integrating its private-noise update kernel against the state measure equals
applying the update to the product of the state and private-input measures](goal). -/
-- @node: bind_privateNoiseUpdateKernel
lemma bind_privateNoiseUpdateKernel
    {X Z Y : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
    (mu : Measure X) (rho : Measure Z) [SFinite rho]
    (F : X × Z → Y) (hF : Measurable F) :
    mu.bind (privateNoiseUpdateKernel rho F hF) = (mu.prod rho).map F := by
  ext s hs
  rw [Measure.bind_apply hs (privateNoiseUpdateKernel rho F hF).aemeasurable,
    Measure.map_apply hF hs, Measure.prod_apply (hs.preimage hF)]
  apply lintegral_congr
  intro x
  change (rho.map (fun z => F (x,z))) s = _
  exact Measure.map_apply (hF.comp measurable_prodMk_left) hs

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- For [a canonical structural causal model](hyp:M), [a node](hyp:i), and
[an intervention](hyp:t), [the canonical node history kernel](goal) is formed by
[taking the marginal law of that node's private noise blocks](step:1) and
[integrating the single-node history update against that law](step:2). -/
-- @node: canonicalNodeHistoryKernel
def canonicalNodeHistoryKernel (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (t : Intervention kind) : Kernel (Joint kind) (Joint kind) := by
  letI := M.latentLaw_probability
  let rho := M.latentLaw.map (restrictLatentFamily (nodeLatentIndices (C := C) i))
  haveI : IsProbabilityMeasure rho :=
    Measure.isProbabilityMeasure_map (restrictLatentFamily_measurable _).aemeasurable
  exact privateNoiseUpdateKernel rho (nodeHistoryUpdate M.toEuclideanSCM i t)
    (nodeHistoryUpdate_measurable M.toEuclideanSCM i t)

-- @node: canonicalNodeHistoryKernel_markov
/-- For [a canonical structural causal model](hyp:M), [a node](hyp:i), and
[an intervention](hyp:t), [the canonical node history kernel assigns a probability
measure to every history](goal). -/
instance canonicalNodeHistoryKernel_markov (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (t : Intervention kind) :
    IsMarkovKernel (canonicalNodeHistoryKernel M i t) := by
  let := M.latentLaw_probability
  have : IsProbabilityMeasure (M.latentLaw.map
      (restrictLatentFamily (nodeLatentIndices (C := C) i))) :=
    Measure.isProbabilityMeasure_map (restrictLatentFamily_measurable _).aemeasurable
  unfold canonicalNodeHistoryKernel
  exact privateNoiseUpdateKernel_markov _ _ _

/-- If [the confounding graph has no hidden confounding](hyp:hnoconf) and
[the model's latent blocks are independent](hyp:hind), then [the history law just
after a node's slot equals the preceding history law integrated against that
node's canonical transition kernel](goal). -/
-- @node: evalSteps_succ_law_eq_bind_node
lemma evalSteps_succ_law_eq_bind_node
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (i : Fin n) (t : Intervention kind) :
    M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (dag.topoOrder i + 1)) =
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (dag.topoOrder i))).bind
        (canonicalNodeHistoryKernel M i t) := by
  let := M.latentLaw_probability
  rw [evalSteps_succ_law_eq_product_update M hnoconf hind i t]
  unfold canonicalNodeHistoryKernel
  exact (bind_privateNoiseUpdateKernel
    (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (dag.topoOrder i)))
    (M.latentLaw.map (restrictLatentFamily (nodeLatentIndices (C := C) i)))
    (nodeHistoryUpdate M.toEuclideanSCM i t)
    (nodeHistoryUpdate_measurable M.toEuclideanSCM i t)).symm

/-- If [no node occupies the given topological slot](hyp:hr), then [the evaluation
history after that slot equals the history before it](goal). -/
-- @node: evalSteps_succ_eq_of_empty_slot
lemma evalSteps_succ_eq_of_empty_slot (M : EuclideanSCM kind dims)
    (t : Intervention kind) (u : Exogenous kind dims) (r : ℕ)
    (hr : ∀ i, M.dag.topoOrder i ≠ r) :
    evalSteps M t u (r+1) = evalSteps M t u r := by
  apply WithLp.ofLp_injective
  funext ⟨i,j⟩
  simp only [evalSteps, WithLp.ofLp_toLp, hr i, if_false]

/-- For [a canonical structural causal model](hyp:M), [an intervention](hyp:t), and
[a topological slot](hyp:r), [the canonical history transition kernel](goal) uses
[the occupying node's transition kernel when the slot is occupied](step:1), or
[the identity kernel when the slot is empty](step:2). -/
-- @node: canonicalHistoryKernel
def canonicalHistoryKernel (M : CanonicalSCM kind dims dag G C)
    (t : Intervention kind) (r : ℕ) : Kernel (Joint kind) (Joint kind) :=
  if h : ∃ i, dag.topoOrder i = r then canonicalNodeHistoryKernel M h.choose t
  else Kernel.id

-- @node: canonicalHistoryKernel_markov
/-- For [a canonical structural causal model](hyp:M), [an intervention](hyp:t), and
[a topological slot](hyp:r), [the canonical history transition kernel assigns a
probability measure to every history](goal). -/
instance canonicalHistoryKernel_markov (M : CanonicalSCM kind dims dag G C)
    (t : Intervention kind) (r : ℕ) : IsMarkovKernel (canonicalHistoryKernel M t r) := by
  unfold canonicalHistoryKernel
  split_ifs <;> infer_instance

/-- If [the confounding graph has no hidden confounding](hyp:hnoconf) and
[the model's latent blocks are independent](hyp:hind), then [the history law after
any slot equals the preceding history law integrated against that slot's canonical
history transition kernel](goal). -/
-- @node: evalSteps_succ_law_eq_bind
lemma evalSteps_succ_law_eq_bind
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (t : Intervention kind) (r : ℕ) :
    M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (r+1)) =
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u r)).bind
        (canonicalHistoryKernel M t r) := by
  unfold canonicalHistoryKernel
  split_ifs with h
  · have hi := h.choose_spec
    simpa only [hi] using evalSteps_succ_law_eq_bind_node M hnoconf hind h.choose t
  · have hr : ∀ i, M.toEuclideanSCM.dag.topoOrder i ≠ r := by
      intro i hi
      exact h ⟨i, hi⟩
    simp only [evalSteps_succ_eq_of_empty_slot M.toEuclideanSCM t _ r hr]
    exact Measure.bind_dirac.symm


/-- For [a stage](hyp:r), [the node types](hyp:kind), and [the directed acyclic graph
fixing their topological order](hyp:dag), [the visited-history domain](goal) consists
of histories in which every categorical node visited before that stage has all
its coordinates equal to one plus a valid label index. -/
-- @node: visitedHistoryDomain
def visitedHistoryDomain (r : ℕ) : Set (Joint kind) :=
  {v | ∀ i k, kind i = .inr k → dag.topoOrder i < r →
    ∃ label : Fin k, ∀ j, v.ofLp ⟨i,j⟩ = (label.val + 1 : ℕ)}

-- @node: visitedHistoryDomain_measurableSet
/-- [The set of histories whose previously visited categorical nodes carry valid
labels is measurable at every stage](goal). -/
lemma visitedHistoryDomain_measurableSet (r : ℕ) :
    MeasurableSet (visitedHistoryDomain (kind := kind) (dag := dag) r) := by
  simp only [visitedHistoryDomain, Set.ofPred_forall, Set.ofPred_exists]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun label => MeasurableSet.iInter fun j =>
        measurableSet_eq_fun (by fun_prop) measurable_const

/-- If [the intervention is admissible](hyp:ht), then [every evaluation history
belongs to the visited-history domain at its evaluation stage](goal). -/
-- @node: evalSteps_mem_visitedHistoryDomain
lemma evalSteps_mem_visitedHistoryDomain (M : EuclideanSCM kind dims)
    (t : Intervention kind) (ht : AdmissibleIntervention kind t)
    (u : Exogenous kind dims) (r : ℕ) :
    evalSteps M t u r ∈ visitedHistoryDomain (dag := M.dag) r := by
  intro i k hi hr
  exact evalSteps_intervention_categorical_label M t ht u i k hi r hr

/-- If [the intervention is admissible](hyp:ht), then [the evaluation history
belongs to its stage's visited-history domain almost surely under its induced law](goal).

A partial history need not be an admissible complete observed vector. -/
-- @node: evalSteps_law_ae_visitedHistoryDomain
lemma evalSteps_law_ae_visitedHistoryDomain (M : EuclideanSCM kind dims)
    (t : Intervention kind) (ht : AdmissibleIntervention kind t) (r : ℕ) :
    ∀ᵐ v ∂M.latentLaw.map (fun u => evalSteps M t u r),
      v ∈ visitedHistoryDomain (dag := M.dag) r := by
  apply (ae_map_iff (evalSteps_measurable M t r).aemeasurable
    (visitedHistoryDomain_measurableSet r)).2
  exact Filter.Eventually.of_forall fun u => evalSteps_mem_visitedHistoryDomain M t ht u r

/-- If [the node occupies the given topological slot](hyp:hr) and [the history belongs
to that stage's visited-history domain](hyp:hv), then [the node's structural input
belongs to its structural domain for every exogenous input vector](goal). -/
-- @node: structuralInput_mem_domain_of_visitedHistory
lemma structuralInput_mem_domain_of_visitedHistory (M : EuclideanSCM kind dims)
    (i : Fin n) (r : ℕ) (hr : M.dag.topoOrder i = r)
    (v : Joint kind) (hv : v ∈ visitedHistoryDomain (dag := M.dag) r)
    (u : Exogenous kind dims) : structuralInput M i v u ∈ M.domain i := by
  refine ⟨?_, Set.mem_univ _⟩
  intro p k hk
  have hp : M.dag.topoOrder p.val < r := by
    rw [← hr]
    exact M.dag.topoOrder_lt _ _ (M.dag.mem_parents.mp p.property)
  exact hv p.val k hk hp


/-- Suppose [the confounding graph has no hidden confounding](hyp:hnoconf),
[the model's latent blocks are independent](hyp:hind),
[the first intervention is admissible](hyp:ht), and [the second intervention is admissible](hyp:ht').
If [the proposed transition coupling couples the two canonical transition laws
at every pair of histories](hyp:hR) and [its expected distance on valid histories
is bounded by a multiple of their distance plus an additive error](hyp:hcost), with
[nonnegative multiplier](hyp:A) and [nonnegative, possibly infinite error](hyp:E), then
[the Wasserstein distance between the next history laws is at most that multiplier
times the current Wasserstein distance plus that error](goal). -/
-- @node: canonical_history_transport_step
lemma canonical_history_transport_step
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (t t' : Intervention kind) (ht : AdmissibleIntervention kind t)
    (ht' : AdmissibleIntervention kind t') (r : ℕ)
    (R : Kernel (Joint kind × Joint kind) (Joint kind × Joint kind))
    (hR : ∀ z, R z ∈ couplings (canonicalHistoryKernel M t r z.1)
      (canonicalHistoryKernel M t' r z.2))
    (A : ℝ≥0) (E : ℝ≥0∞)
    (hcost : ∀ z : Joint kind × Joint kind, z.1 ∈ visitedHistoryDomain (dag := dag) r →
      z.2 ∈ visitedHistoryDomain (dag := dag) r →
      (∫⁻ w : Joint kind × Joint kind, edist w.1 w.2 ∂(R z)) ≤ (A : ℝ≥0∞) * edist z.1 z.2 + E) :
    wasserstein1
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (r+1)))
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t' u (r+1))) ≤
      (A : ℝ≥0∞) * wasserstein1
        (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u r))
        (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t' u r)) + E := by
  let := M.latentLaw_probability
  have hmu : IsProbabilityMeasure
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u r)) :=
    Measure.isProbabilityMeasure_map (evalSteps_measurable M.toEuclideanSCM t r).aemeasurable
  have hnu : IsProbabilityMeasure
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t' u r)) :=
    Measure.isProbabilityMeasure_map (evalSteps_measurable M.toEuclideanSCM t' r).aemeasurable
  rw [evalSteps_succ_law_eq_bind M hnoconf hind t r,
    evalSteps_succ_law_eq_bind M hnoconf hind t' r]
  exact approximation_wasserstein_bind_cross_bound_on
    (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u r))
    (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t' u r)) _ _
    (evalSteps_law_ae_visitedHistoryDomain M.toEuclideanSCM t ht r)
    (evalSteps_law_ae_visitedHistoryDomain M.toEuclideanSCM t' ht' r)
    _ _ R hR A E hcost

end
end Papers.TbsNeuralCausalPi
