module
public import Papers.TbsNeuralCausalPi.Helpers.CategoricalHistoryCost
public import Papers.TbsNeuralCausalPi.Helpers.InterventionalMoments
public import Papers.TbsNeuralCausalPi.Helpers.ActiveNodeTransport
public import Mathlib.Probability.Kernel.Composition.Prod
/-! # Local couplings for canonical history transitions

Continuous transitions share their private noise; categorical transitions use
maximal couplings. Off the carrying domain an independent product suffices.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
-- @node: wasserstein_bind_cross_bound_local
/-- Suppose [the first carrying set is measurable](hyp:hS), [the second carrying set is
measurable](hyp:hT), [the first initial law is concentrated on the first set](hyp:hmu),
and [the second initial law is concentrated on the second set](hyp:hnu).
If [the proposed kernel couples the two transitions on these sets](hyp:hR), with
[a nonnegative distance multiplier](hyp:A) and [a nonnegative, possibly infinite error
allowance](hyp:E) such that [its expected distance is at most the multiplier times
the input distance plus the allowance](hyp:hcost), then [the Wasserstein distance
between the updated laws is at most the multiplier times the initial Wasserstein
distance plus the allowance](goal). -/
lemma wasserstein_bind_cross_bound_local
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hmu : ∀ᵐ x ∂mu, x ∈ S) (hnu : ∀ᵐ x ∂nu, x ∈ T)
    (kappa eta : Kernel X Y) [IsMarkovKernel kappa] [IsMarkovKernel eta]
    (R : Kernel (X × X) (Y × Y))
    (hR : ∀ z, z.1 ∈ S → z.2 ∈ T → R z ∈ couplings (kappa z.1) (eta z.2))
    (A : ℝ≥0) (E : ℝ≥0∞)
    (hcost : ∀ z : X × X, z.1 ∈ S → z.2 ∈ T →
      (∫⁻ w : Y × Y, edist w.1 w.2 ∂(R z)) ≤
      (A : ℝ≥0∞) * edist z.1 z.2 + E) :
    wasserstein1 (mu.bind kappa) (nu.bind eta) ≤
      (A : ℝ≥0∞) * wasserstein1 mu nu + E := by
  let V : Set (X × X) := {z | z.1 ∈ S ∧ z.2 ∈ T}
  have hV : MeasurableSet V := (hS.preimage measurable_fst).inter (hT.preimage measurable_snd)
  let Q := (kappa.prodMkRight X).prod (eta.prodMkLeft X)
  let R' := Kernel.piecewise hV R Q
  apply approximation_wasserstein_bind_cross_bound_on mu nu S T hmu hnu kappa eta R'
  · intro z
    by_cases hz : z ∈ V
    · simpa only [R', Kernel.piecewise_apply, hz, if_true] using hR z hz.1 hz.2
    · have he : R' z = (kappa z.1).prod (eta z.2) := by
        simp [R', Kernel.piecewise_apply, hz, Q, Kernel.prod_apply]
      rw [he]
      exact ⟨inferInstance, by simp, by simp⟩
  · intro z hz hz'
    have hmem : z ∈ V := ⟨hz,hz'⟩
    simpa only [R', Kernel.piecewise_apply, hmem, if_true] using hcost z hz hz'

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)}

-- @node: nodeHistoryUpdate_dist_le
/-- [The distance between two histories after updating one node is at most their
previous distance plus the distance between the two replacement values, using each
intervention's assigned value when present and its structural output otherwise](goal). -/
lemma nodeHistoryUpdate_dist_le (M : EuclideanSCM kind dims) (i : Fin n)
    (t t' : Intervention kind) (v w : Joint kind) (u u' : Exogenous kind dims) :
    dist (nodeHistoryUpdate M i t (v,u)) (nodeHistoryUpdate M i t' (w,u')) ≤
      dist v w + dist ((t i).getD (nodeValue M i v u))
        ((t' i).getD (nodeValue M i w u')) := by
  let d := dist ((t i).getD (nodeValue M i v u)) ((t' i).getD (nodeValue M i w u'))
  rw [PiLp.dist_eq_of_L1, PiLp.dist_eq_of_L1, Fintype.sum_sigma, Fintype.sum_sigma]
  calc
    _ ≤ ∑ j, ((∑ l : Fin (valueDim (kind j)), dist (v.ofLp ⟨j,l⟩) (w.ofLp ⟨j,l⟩)) +
        if j = i then d else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = i
      · subst j
        simp only [nodeHistoryUpdate, WithLp.ofLp_toLp, dite_true, Fin.cast_refl, if_true]
        simp only [id_eq]
        rw [← PiLp.dist_eq_of_L1]
        change d ≤ _ + d
        exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => dist_nonneg)
      · simp only [nodeHistoryUpdate, WithLp.ofLp_toLp, hj, dite_false, if_false, add_zero]
        exact le_rfl
    _ = _ := by rw [Finset.sum_add_distrib]; simp [d]

-- @node: nodeValue_continuous_dist_same_noise_le
/-- If [the node has a continuous output of the given dimension](hyp:hi),
[a nonnegative constant](hyp:L) [bounds the continuous mechanisms' Lipschitz
constants](hyp:hcont), and [the first structural input lies in the node's domain](hyp:hv)
and [the second structural input does too](hyp:hw), then [the distance between the
two outputs at shared noise is at most that constant times the history distance](goal). -/
lemma nodeValue_continuous_dist_same_noise_le
    (M : EuclideanSCM kind dims) (i : Fin n) (d : ℕ) (hi : kind i = Sum.inl d)
    (L : ℝ≥0) (hcont : ContinuousMechanismsLipschitz M L)
    (v w : Joint kind) (u : Exogenous kind dims)
    (hv : structuralInput M i v u ∈ M.domain i)
    (hw : structuralInput M i w u ∈ M.domain i) :
    dist (nodeValue M i v u) (nodeValue M i w u) ≤ (L : ℝ) * dist v w := by
  have he : dist (nodeValue M i v u) (nodeValue M i w u) =
      dist (M.continuousMap i (structuralInput M i v u))
        (M.continuousMap i (structuralInput M i w u)) := by
    rw [PiLp.dist_eq_of_L1, PiLp.dist_eq_of_L1]
    simp_rw [nodeValue_continuous_coordinate M i d hi]
    have hdim : valueDim (kind i) = outputDim (kind i) := by simp [hi, valueDim, outputDim]
    convert Function.Bijective.sum_comp
      (show Function.Bijective (Fin.cast hdim) from
        ⟨Fin.cast_injective _, fun j => ⟨Fin.cast hdim.symm j, by simp⟩⟩)
      (fun j => dist ((M.continuousMap i (structuralInput M i v u)).ofLp j)
        ((M.continuousMap i (structuralInput M i w u)).ofLp j)) using 1
  rw [he]
  exact ((hcont i d hi).dist_le_mul _ hv _ hw).trans
    (mul_le_mul_of_nonneg_left (structuralInput_dist_same_noise_le M i v w u) L.coe_nonneg)

-- @node: canonicalSynchronousHistoryCoupling
/-- For [a canonical structural causal model](hyp:M), [a node to update](hyp:i),
and [two interventions](hyp:t,t'), the [synchronous history coupling kernel](goal)
updates both input histories using the same draw from the model's latent law. -/
def canonicalSynchronousHistoryCoupling
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (t t' : Intervention kind) :
    Kernel (Joint kind × Joint kind) (Joint kind × Joint kind) := by
  letI := M.latentLaw_probability
  exact privateNoiseUpdateKernel M.latentLaw
    (fun z => (nodeHistoryUpdate M.toEuclideanSCM i t (z.1.1,z.2),
      nodeHistoryUpdate M.toEuclideanSCM i t' (z.1.2,z.2))) (by fun_prop)

-- @node: canonicalSynchronousHistoryCoupling_coupling
/-- [The synchronous history update law has as its two marginals the respective
node transition laws under the two interventions at the two input histories](goal). -/
lemma canonicalSynchronousHistoryCoupling_coupling
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (t t' : Intervention kind)
    (v w : Joint kind) :
    canonicalSynchronousHistoryCoupling M i t t' (v,w) ∈
      couplings (canonicalNodeHistoryKernel M i t v) (canonicalNodeHistoryKernel M i t' w) := by
  letI := M.latentLaw_probability
  let F := fun u => (nodeHistoryUpdate M.toEuclideanSCM i t (v,u),
    nodeHistoryUpdate M.toEuclideanSCM i t' (w,u))
  have hF : Measurable F := by fun_prop
  change M.latentLaw.map F ∈ _
  refine ⟨Measure.isProbabilityMeasure_map hF.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hF, canonicalNodeHistoryKernel_eq_map_update]
    rfl
  · rw [Measure.map_map measurable_snd hF, canonicalNodeHistoryKernel_eq_map_update]
    rfl

-- @node: canonicalSynchronousHistoryCoupling_continuous_cost_le
/-- If [the node is continuous with the given output dimension](hyp:hi),
[the first intervention leaves it unassigned](hyp:hti) and [the second does too](hyp:hti'),
and [a nonnegative constant](hyp:L) [bounds the continuous mechanisms' Lipschitz
constants](hyp:hcont), then, for [a first history in the visited-history domain just
before this node](hyp:hv) and [a second history in that domain](hyp:hw), [the synchronous
coupling's expected distance is at most the initial distance multiplied by one plus
that constant](goal). -/
lemma canonicalSynchronousHistoryCoupling_continuous_cost_le
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (d : ℕ) (hi : kind i = Sum.inl d)
    (t t' : Intervention kind) (hti : t i = none) (hti' : t' i = none)
    (L : ℝ≥0) (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (v w : Joint kind)
    (hv : v ∈ visitedHistoryDomain (dag := dag) (dag.topoOrder i))
    (hw : w ∈ visitedHistoryDomain (dag := dag) (dag.topoOrder i)) :
    (∫⁻ z, edist z.1 z.2 ∂canonicalSynchronousHistoryCoupling M i t t' (v,w)) ≤
      ((1+L : ℝ≥0) : ℝ≥0∞) * edist v w := by
  letI := M.latentLaw_probability
  change (∫⁻ z, edist z.1 z.2 ∂M.latentLaw.map
    (fun u => (nodeHistoryUpdate M.toEuclideanSCM i t (v,u),
      nodeHistoryUpdate M.toEuclideanSCM i t' (w,u)))) ≤ _
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  have hpoint (u : Exogenous kind dims) :
      edist (nodeHistoryUpdate M.toEuclideanSCM i t (v,u))
        (nodeHistoryUpdate M.toEuclideanSCM i t' (w,u)) ≤
          ((1+L : ℝ≥0) : ℝ≥0∞) * edist v w := by
    have hn := nodeValue_continuous_dist_same_noise_le M.toEuclideanSCM i d hi L hcont v w u
      (structuralInput_mem_domain_of_visitedHistory M.toEuclideanSCM i _ rfl v hv u)
      (structuralInput_mem_domain_of_visitedHistory M.toEuclideanSCM i _ rfl w hw u)
    have hh := nodeHistoryUpdate_dist_le M.toEuclideanSCM i t t' v w u u
    simp only [hti, hti', Option.getD_none] at hh
    have hd : dist (nodeHistoryUpdate M.toEuclideanSCM i t (v,u))
        (nodeHistoryUpdate M.toEuclideanSCM i t' (w,u)) ≤ (1+(L : ℝ)) * dist v w := by
      nlinarith
    rw [edist_dist, edist_dist, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by simpa using hd)
  calc
    _ ≤ ∫⁻ _u, ((1+L : ℝ≥0) : ℝ≥0∞) * edist v w ∂M.latentLaw :=
      lintegral_mono hpoint
    _ = _ := by simp


-- @node: canonicalSynchronousHistoryCoupling_assigned_cost_le
/-- If [the first intervention assigns the first specified value to the node](hyp:hti)
and [the second assigns the second specified value](hyp:hti'), then [the synchronous
coupling's expected history distance is at most the initial history distance plus
the distance between those assigned values](goal). -/
lemma canonicalSynchronousHistoryCoupling_assigned_cost_le
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (t t' : Intervention kind)
    (x y : L1Vec (valueDim (kind i))) (hti : t i = some x) (hti' : t' i = some y)
    (v w : Joint kind) :
    (∫⁻ z, edist z.1 z.2 ∂canonicalSynchronousHistoryCoupling M i t t' (v,w)) ≤
      edist v w + edist x y := by
  letI := M.latentLaw_probability
  change (∫⁻ z, edist z.1 z.2 ∂M.latentLaw.map
    (fun u => (nodeHistoryUpdate M.toEuclideanSCM i t (v,u),
      nodeHistoryUpdate M.toEuclideanSCM i t' (w,u)))) ≤ _
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  have hpoint (u : Exogenous kind dims) :
      edist (nodeHistoryUpdate M.toEuclideanSCM i t (v,u))
        (nodeHistoryUpdate M.toEuclideanSCM i t' (w,u)) ≤ edist v w + edist x y := by
    have h := nodeHistoryUpdate_dist_le M.toEuclideanSCM i t t' v w u u
    simp only [hti, hti', Option.getD_some] at h
    simpa only [edist_dist, ENNReal.ofReal_add dist_nonneg dist_nonneg] using
      ENNReal.ofReal_le_ofReal h
  exact (lintegral_mono hpoint).trans_eq (by simp)

-- @node: canonical_categorical_history_transport_step
/-- Suppose [there is no hidden confounding](hyp:hnoconf), [the latent blocks are
independent](hyp:hind), and [the node is categorical with the given number of labels](hyp:hi).
For [an admissible first intervention](hyp:ht) and [an admissible second intervention](hyp:ht'),
[both leaving this node unassigned](hyp:hti,hti'), if [a nonnegative constant](hyp:L)
[bounds the categorical propensities' Lipschitz constants](hyp:hprop), then [the
Wasserstein distance after this node is at most the distance before it multiplied
by one plus that constant times the number of labels reduced by one and divided by two](goal). -/
lemma canonical_categorical_history_transport_step
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    (t t' : Intervention kind) (ht : AdmissibleIntervention kind t)
    (ht' : AdmissibleIntervention kind t') (hti : t i = none) (hti' : t' i = none)
    (L : ℝ≥0) (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L) :
    wasserstein1
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (dag.topoOrder i+1)))
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t' u (dag.topoOrder i+1))) ≤
      ((1 + (k-1 : ℕ) * L / 2 : ℝ≥0) : ℝ≥0∞) * wasserstein1
        (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (dag.topoOrder i)))
        (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t' u (dag.topoOrder i))) := by
  letI := M.latentLaw_probability
  haveI : IsProbabilityMeasure
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (dag.topoOrder i))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t' u (dag.topoOrder i))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [evalSteps_succ_law_eq_bind_node M hnoconf hind i t,
    evalSteps_succ_law_eq_bind_node M hnoconf hind i t']
  have h := wasserstein_bind_cross_bound_local
    (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (dag.topoOrder i)))
    (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t' u (dag.topoOrder i)))
    (visitedHistoryDomain (dag := dag) (dag.topoOrder i))
    (visitedHistoryDomain (dag := dag) (dag.topoOrder i))
    (visitedHistoryDomain_measurableSet _) (visitedHistoryDomain_measurableSet _)
    (evalSteps_law_ae_visitedHistoryDomain M.toEuclideanSCM t ht _)
    (evalSteps_law_ae_visitedHistoryDomain M.toEuclideanSCM t' ht' _)
    (canonicalNodeHistoryKernel M i t) (canonicalNodeHistoryKernel M i t')
    (canonicalCategoricalHistoryCoupling M i k hi)
    (fun z hz hz' => canonicalCategoricalHistoryCoupling_coupling M i k hi t t' hti hti' _ _ hz hz')
    (1 + (k-1 : ℕ) * L / 2) 0 (by
      intro z hz hz'
      have hh := canonicalCategoricalHistoryCoupling_cost_le M i k hi L hprop z.1 z.2 hz hz'
      simpa only [add_zero, NNReal.coe_add, NNReal.coe_one, NNReal.coe_div, NNReal.coe_mul,
        NNReal.coe_natCast, NNReal.coe_ofNat, ← ENNReal.ofReal_coe_nnreal,
        mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hh)
  simpa only [add_zero] using h

-- @node: categoricalFactor_one_le
/-- [The uniform categorical factor is at least one](goal). -/
lemma categoricalFactor_one_le : 1 ≤ categoricalFactor kind := le_max_left _ _

-- @node: categoricalFactor_label_le
/-- If [a node is categorical with the given number of labels](hyp:hi), then
[the number of labels, reduced by one and divided by two, is at most the uniform
categorical factor](goal). -/
lemma categoricalFactor_label_le (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k) :
    (k-1 : ℕ) / 2 ≤ categoricalFactor kind := by
  have hb : BddAbove (Set.range (fun i : Fin n => match kind i with
      | .inl _ => (0 : ℝ) | .inr k => (k-1 : ℕ) / 2)) := (Set.finite_range _).bddAbove
  have h := le_csSup hb (Set.mem_range_self i)
  have hh : ((k-1 : ℕ) : ℝ) / 2 ≤ sSup (Set.range (fun i : Fin n => match kind i with
      | .inl _ => (0 : ℝ) | .inr k => (k-1 : ℕ) / 2)) := by simpa only [hi] using h
  exact hh.trans (le_max_right _ _)

-- @node: historyExpansion
/-- For [the collection of node types](hyp:kind) and [a nonnegative Lipschitz
constant](hyp:L), the [history expansion factor](goal) is one plus the product of
that constant and the uniform categorical factor. -/
def historyExpansion (kind : Fin n → NodeKind) (L : ℝ≥0) : ℝ≥0 :=
  ⟨1 + (L : ℝ) * categoricalFactor kind, by
    have hD := categoricalFactor_one_le (kind := kind)
    positivity⟩

-- @node: historyExpansion_one_le
/-- For [any nonnegative Lipschitz constant](hyp:L), [the history expansion factor
is at least one](goal). -/
lemma historyExpansion_one_le (L : ℝ≥0) : 1 ≤ historyExpansion kind L := by
  change (1 : ℝ) ≤ 1 + (L : ℝ) * categoricalFactor kind
  have hD := categoricalFactor_one_le (kind := kind)
  nlinarith [L.coe_nonneg]

-- @node: canonical_node_history_coupling_exists
/-- Given [a nonnegative constant](hyp:L) bounding [the continuous mechanisms'
Lipschitz constants](hyp:hcont) and [the categorical propensities' Lipschitz
constants](hyp:hprop), and [two families of assigned node values](hyp:x,y) on a
common intervention set, [there exists a kernel coupling the two node transitions
for every pair of histories in the visited-history domain, whose expected distance
is at most the history expansion factor times their initial distance plus the
distance between the assigned values at this node if it is intervened on, and zero
additional error otherwise](goal). -/
lemma canonical_node_history_coupling_exists
    (M : CanonicalSCM kind dims dag G C) (L : ℝ≥0)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (S : Finset (Fin n)) (x y : ∀ i, L1Vec (valueDim (kind i))) (i : Fin n) :
    let t : Intervention kind := fun j => if j ∈ S then some (x j) else none
    let t' : Intervention kind := fun j => if j ∈ S then some (y j) else none
    ∃ R : Kernel (Joint kind × Joint kind) (Joint kind × Joint kind),
      (∀ z : Joint kind × Joint kind,
        z.1 ∈ visitedHistoryDomain (dag := dag) (dag.topoOrder i) →
        z.2 ∈ visitedHistoryDomain (dag := dag) (dag.topoOrder i) →
        R z ∈ couplings (canonicalNodeHistoryKernel M i t z.1)
          (canonicalNodeHistoryKernel M i t' z.2)) ∧
      ∀ z : Joint kind × Joint kind,
        z.1 ∈ visitedHistoryDomain (dag := dag) (dag.topoOrder i) →
        z.2 ∈ visitedHistoryDomain (dag := dag) (dag.topoOrder i) →
        (∫⁻ w : Joint kind × Joint kind, edist w.1 w.2 ∂(R z)) ≤
          (historyExpansion kind L : ℝ≥0∞) * edist z.1 z.2 +
            if i ∈ S then edist (x i) (y i) else 0 := by
  dsimp only
  let t : Intervention kind := fun j => if j ∈ S then some (x j) else none
  let t' : Intervention kind := fun j => if j ∈ S then some (y j) else none
  have hA : (1 : ℝ≥0∞) ≤ historyExpansion kind L := by
    exact_mod_cast historyExpansion_one_le (kind := kind) L
  by_cases hs : i ∈ S
  · refine ⟨canonicalSynchronousHistoryCoupling M i t t', ?_, ?_⟩
    · intro z _ _
      exact canonicalSynchronousHistoryCoupling_coupling M i t t' z.1 z.2
    · intro z _ _
      have h := canonicalSynchronousHistoryCoupling_assigned_cost_le M i t t' (x i) (y i)
        (by simp [t, hs]) (by simp [t', hs]) z.1 z.2
      simp only [hs, if_true]
      refine h.trans ?_
      have hh : edist z.1 z.2 ≤ (historyExpansion kind L : ℝ≥0∞) * edist z.1 z.2 := by
        calc
          edist z.1 z.2 = (1 : ℝ≥0∞) * edist z.1 z.2 := (one_mul _).symm
          _ ≤ _ := by gcongr
      gcongr
  · have ht : t i = none := by simp [t, hs]
    have ht' : t' i = none := by simp [t', hs]
    have hk : (∃ d, kind i = Sum.inl d) ∨ ∃ k, kind i = Sum.inr k := by
      cases hi : kind i with
      | inl d => exact Or.inl ⟨d,rfl⟩
      | inr k => exact Or.inr ⟨k,rfl⟩
    rcases hk with ⟨d,hi⟩ | ⟨k,hi⟩
    ·
      refine ⟨canonicalSynchronousHistoryCoupling M i t t', ?_, ?_⟩
      · intro z _ _
        exact canonicalSynchronousHistoryCoupling_coupling M i t t' z.1 z.2
      · intro z hz hz'
        have h := canonicalSynchronousHistoryCoupling_continuous_cost_le M i d hi t t' ht ht'
          L hcont z.1 z.2 hz hz'
        have hcoef : (1+L : ℝ≥0) ≤ historyExpansion kind L := by
          change (1 : ℝ) + L ≤ 1 + (L : ℝ) * categoricalFactor kind
          have hD := categoricalFactor_one_le (kind := kind)
          nlinarith [L.coe_nonneg]
        simp only [hs, if_false, add_zero]
        refine h.trans ?_
        have hcoef' : ((1+L : ℝ≥0) : ℝ≥0∞) ≤ (historyExpansion kind L : ℝ≥0∞) :=
          by exact_mod_cast hcoef
        gcongr
    ·
      refine ⟨canonicalCategoricalHistoryCoupling M i k hi, ?_, ?_⟩
      · intro z hz hz'
        exact canonicalCategoricalHistoryCoupling_coupling M i k hi t t' ht ht' _ _ hz hz'
      · intro z hz hz'
        have h := canonicalCategoricalHistoryCoupling_cost_le M i k hi L hprop z.1 z.2 hz hz'
        have hcoef : ENNReal.ofReal (1 + (k-1 : ℕ) / 2 * (L : ℝ)) ≤
            (historyExpansion kind L : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_coe_nnreal]
          apply ENNReal.ofReal_le_ofReal
          change _ ≤ 1 + (L : ℝ) * categoricalFactor kind
          have hD := categoricalFactor_label_le i k hi
          nlinarith [mul_le_mul_of_nonneg_left hD L.coe_nonneg]
        simp only [hs, if_false, add_zero]
        refine h.trans ?_
        gcongr

-- @node: canonical_node_history_distance_step
/-- Suppose [there is no hidden confounding](hyp:hnoconf), [the latent blocks are
independent](hyp:hind), and [a nonnegative constant](hyp:L) bounds [the continuous
mechanisms' Lipschitz constants](hyp:hcont) and [the categorical propensities'
Lipschitz constants](hyp:hprop). For [two assignment families](hyp:x,y) on a common
intervention set, with [the first induced intervention admissible](hyp:ht) and
[the second admissible](hyp:ht'), [the Wasserstein distance after this node is at
most the history expansion factor times the distance before it, plus the distance
between its assigned values if it is intervened on, and zero additional error otherwise](goal). -/
lemma canonical_node_history_distance_step
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (hind : LatentBlocksIndependent M.toEuclideanSCM) (L : ℝ≥0)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (S : Finset (Fin n)) (x y : ∀ i, L1Vec (valueDim (kind i)))
    (ht : AdmissibleIntervention kind (fun i => if i ∈ S then some (x i) else none))
    (ht' : AdmissibleIntervention kind (fun i => if i ∈ S then some (y i) else none))
    (i : Fin n) :
    let t : Intervention kind := fun i => if i ∈ S then some (x i) else none
    let t' : Intervention kind := fun i => if i ∈ S then some (y i) else none
    wasserstein1
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (dag.topoOrder i+1)))
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t' u (dag.topoOrder i+1))) ≤
      (historyExpansion kind L : ℝ≥0∞) * wasserstein1
        (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (dag.topoOrder i)))
        (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t' u (dag.topoOrder i))) +
        if i ∈ S then edist (x i) (y i) else 0 := by
  dsimp only
  letI := M.latentLaw_probability
  let t : Intervention kind := fun i => if i ∈ S then some (x i) else none
  let t' : Intervention kind := fun i => if i ∈ S then some (y i) else none
  haveI : IsProbabilityMeasure
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (dag.topoOrder i))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t' u (dag.topoOrder i))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [evalSteps_succ_law_eq_bind_node M hnoconf hind i t,
    evalSteps_succ_law_eq_bind_node M hnoconf hind i t']
  obtain ⟨R,hR,hcost⟩ := canonical_node_history_coupling_exists M L hcont hprop S x y i
  exact wasserstein_bind_cross_bound_local
    (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (dag.topoOrder i)))
    (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t' u (dag.topoOrder i))) _ _
    (visitedHistoryDomain_measurableSet _) (visitedHistoryDomain_measurableSet _)
    (evalSteps_law_ae_visitedHistoryDomain M.toEuclideanSCM t ht _)
    (evalSteps_law_ae_visitedHistoryDomain M.toEuclideanSCM t' ht' _)
    _ _ R hR _ _ hcost

-- @node: canonical_assignment_history_transport
/-- Suppose [there is no hidden confounding](hyp:hnoconf), [the latent blocks are
independent](hyp:hind), and [a nonnegative constant](hyp:L) bounds [the continuous
mechanisms' Lipschitz constants](hyp:hcont) and [the categorical propensities'
Lipschitz constants](hyp:hprop). For [two assignment families](hyp:x,y) on a common
intervention set, with [the first induced intervention admissible](hyp:ht) and
[the second admissible](hyp:ht'), [the Wasserstein distance between the full
interventional laws is at most the history expansion factor raised to the number
of nodes times the sum of distances between assigned values on the intervention set](goal). -/
lemma canonical_assignment_history_transport
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (hind : LatentBlocksIndependent M.toEuclideanSCM) (L : ℝ≥0)
    (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (hprop : CategoricalPropensityLipschitz M.toEuclideanSCM M.f L)
    (S : Finset (Fin n)) (x y : ∀ i, L1Vec (valueDim (kind i)))
    (ht : AdmissibleIntervention kind (fun i => if i ∈ S then some (x i) else none))
    (ht' : AdmissibleIntervention kind (fun i => if i ∈ S then some (y i) else none)) :
    wasserstein1
      (M.latentLaw.map (intervenedEval M.toEuclideanSCM
        (fun i => if i ∈ S then some (x i) else none)))
      (M.latentLaw.map (intervenedEval M.toEuclideanSCM
        (fun i => if i ∈ S then some (y i) else none))) ≤
      (historyExpansion kind L : ℝ≥0∞)^n * ∑ i ∈ S, edist (x i) (y i) := by
  letI := M.latentLaw_probability
  let t : Intervention kind := fun i => if i ∈ S then some (x i) else none
  let t' : Intervention kind := fun i => if i ∈ S then some (y i) else none
  let E := fun r => wasserstein1
    (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u r))
    (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t' u r))
  have hzero : E 0 = 0 := by
    have hc : Measure.dirac ((0 : Joint kind), (0 : Joint kind)) ∈
        couplings (Measure.dirac 0) (Measure.dirac 0) := ⟨inferInstance, by simp, by simp⟩
    have hh : wasserstein1 (Measure.dirac (0 : Joint kind)) (Measure.dirac 0) ≤ 0 := by
      rw [wasserstein1_eq_couplings]
      exact iInf_le_of_le ⟨_,hc⟩ (by simp)
    simpa only [E, evalSteps, Measure.map_const, measure_univ, one_smul] using
      le_antisymm hh bot_le
  have hstep := canonical_node_history_distance_step M hnoconf hind L hcont hprop S x y ht ht'
  have hempty (r : ℕ) (hr : ∀ i, dag.topoOrder i ≠ r) : E (r+1) = E r := by
    simp only [E, evalSteps_succ_eq_of_empty_slot M.toEuclideanSCM _ _ r hr]
  have hA : (1 : ℝ≥0∞) ≤ historyExpansion kind L := by
    exact_mod_cast historyExpansion_one_le (kind := kind) L
  have h := active_node_transport_uniform_bound dag.topoOrder dag.topoOrder_injective E
    (historyExpansion kind L : ℝ≥0∞) hA
    (fun i => if i ∈ S then edist (x i) (y i) else 0) hzero hstep hempty (n*n+n)
  change E (n*n+n) ≤ _
  simpa only [Fintype.card_fin, Finset.sum_ite_mem, Finset.univ_inter] using h

end
end Papers.TbsNeuralCausalPi
