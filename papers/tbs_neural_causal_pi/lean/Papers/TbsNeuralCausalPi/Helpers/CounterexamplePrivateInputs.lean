module
public import Papers.TbsNeuralCausalPi.Helpers.CounterexampleSelectionMoments
/-! # Private inputs of arbitrary unconfounded backdoor models

The statistical definition of the bidirected graph permits deterministic shared
blocks. Their almost surely constant values preserve independence of the actual
private-input vectors; disjoint incidence is not assumed.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

/-- For [a structural causal model](hyp:M) and [a set of nodes](hyp:S),
[the retained latent indices](goal) are the shared blocks read by at least one
node in the set, together with the intrinsic noises of those nodes. -/
-- @node: nodeSetLatentIndices
def nodeSetLatentIndices (M : EuclideanSCM kind dims) (S : Finset (Fin n)) :
    Finset (Fin b ⊕ Fin n) :=
  Finset.univ.filter (fun k => match k with
    | .inl j => ∃ i ∈ S, j ∈ M.incidence i
    | .inr i => i ∈ S)

/-- If [the model's latent blocks are independent](hyp:hind) and
[every named block shared by the two index sets is almost surely constant](hyp:hc),
[the two exogenous vectors obtained by retaining the respective index sets are
independent under the latent law](goal). -/
-- @node: restrictLatentFamily_indepFun_of_constant_overlap
lemma restrictLatentFamily_indepFun_of_constant_overlap (M : EuclideanSCM kind dims)
    (hind : LatentBlocksIndependent M) (S R : Finset (Fin b ⊕ Fin n))
    (hc : ∀ k ∈ S ∩ R, ∃ a, ∀ᵐ u ∂M.latentLaw, namedLatent M k u = a) :
    IndepFun (restrictLatentFamily (kind := kind) (dims := dims) S)
      (restrictLatentFamily R) M.latentLaw := by
  let restore (T : Finset (Fin b ⊕ Fin n))
      (w : ∀ k : T, L1Vec (fullLatentDim kind dims k.val)) : Exogenous kind dims :=
    WithLp.toLp 1 (fun c => match c with
      | .inl ⟨j,k⟩ => if h : Sum.inl j ∈ T then (w ⟨.inl j,h⟩).ofLp k else 0
      | .inr ⟨i,k⟩ => if h : Sum.inr i ∈ T then (w ⟨.inr i,h⟩).ofLp k else 0)
  have hm (T : Finset (Fin b ⊕ Fin n)) : Measurable (restore T) := by
    first | fun_prop | skip
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro (⟨j,k⟩ | ⟨i,k⟩) <;> dsimp [restore] <;> split_ifs <;> fun_prop
  have hn (k : Fin b ⊕ Fin n) : Measurable (namedLatent M k) := by
    cases k <;> fun_prop [namedLatent, blockProjection, categoricalNoise]
  have h := (canonical_indepFun_overlapping_finsets hind hn S R hc).comp (hm S) (hm R)
  have he (T : Finset (Fin b ⊕ Fin n)) :
      restore T ∘ (fun u k => namedLatent M k.val u) = restrictLatentFamily T := by
    funext u
    apply WithLp.ofLp_injective
    funext c
    rcases c with ⟨j,k⟩ | ⟨i,k⟩ <;>
      simp [restore, restrictLatentFamily, namedLatent, blockProjection, categoricalNoise]
  simpa only [he] using h

/-- If [the model's latent blocks are independent](hyp:hind),
[its bidirected graph has no edges](hyp:hgraph), and [the two node sets are
disjoint](hyp:hSR), then [the exogenous vectors retaining the inputs of the
respective node sets are independent under the latent law](goal).

Shared deterministic blocks are permitted. -/
-- @node: nodeSet_private_inputs_independent
lemma nodeSet_private_inputs_independent (M : EuclideanSCM kind dims)
    (hind : LatentBlocksIndependent M) (hgraph : (causalGraph M).2 = ⊥)
    (S R : Finset (Fin n)) (hSR : Disjoint S R) :
    IndepFun (restrictLatentFamily (nodeSetLatentIndices M S))
      (restrictLatentFamily (nodeSetLatentIndices M R)) M.latentLaw := by
  apply restrictLatentFamily_indepFun_of_constant_overlap M hind
  intro k hk
  obtain ⟨hS, hR⟩ := Finset.mem_inter.mp hk
  cases k with
  | inl k =>
    obtain ⟨i, hi, hki⟩ := (Finset.mem_filter.mp hS).2
    obtain ⟨j, hj, hkj⟩ := (Finset.mem_filter.mp hR).2
    have hij : i ≠ j := by
      intro he
      subst j
      exact Finset.disjoint_left.mp hSR hi hj
    have hc : IndepFun (blockProjection k) (blockProjection k) M.latentLaw := by
      by_contra hdep
      have hedge := (causalGraph_adj_iff_shared_dependent_block M hind i j).mpr
        ⟨hij, k, hki, hkj, hdep⟩
      rw [hgraph] at hedge
      exact hedge
    exact canonical_self_independent_block_ae_const M k hc
  | inr i =>
    exact (Finset.disjoint_left.mp hSR (Finset.mem_filter.mp hS).2
      (Finset.mem_filter.mp hR).2).elim

/-- If [the node belongs to the retained set](hyp:hi) and [the shared block is
read by that node](hyp:hk), then [masking the exogenous vector to the inputs of
the retained nodes preserves the specified coordinate of that block](goal). -/
-- @node: nodeSet_mask_block
lemma nodeSet_mask_block (M : EuclideanSCM kind dims) (S : Finset (Fin n))
    (i : Fin n) (hi : i ∈ S) (k : Fin b) (hk : k ∈ M.incidence i)
    (u : Exogenous kind dims) (j : Fin (dims k)) :
    (restrictLatentFamily (nodeSetLatentIndices M S) u).ofLp (.inl ⟨k,j⟩) =
      u.ofLp (.inl ⟨k,j⟩) := by
  have hm : Sum.inl k ∈ nodeSetLatentIndices M S := by
    simp only [nodeSetLatentIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, hi, hk⟩
  simp [restrictLatentFamily, hm]

-- @node: nodeSet_mask_noise
/-- If [the node belongs to the retained set](hyp:hi), then [masking the
exogenous vector to the inputs of the retained nodes preserves that node's
categorical noise vector](goal). -/
lemma nodeSet_mask_noise (M : EuclideanSCM kind dims) (S : Finset (Fin n))
    (i : Fin n) (hi : i ∈ S) (u : Exogenous kind dims) :
    categoricalNoise i (restrictLatentFamily (nodeSetLatentIndices M S) u) =
      categoricalNoise i u := by
  have hm : Sum.inr i ∈ nodeSetLatentIndices M S := by
    simpa [nodeSetLatentIndices] using hi
  apply WithLp.ofLp_injective
  funext k
  simp [categoricalNoise, restrictLatentFamily, hm]

/-- If [every node left unassigned by the intervention belongs to the retained
set](hyp:ht), then [evaluating the intervention after masking the exogenous
vector to that set's inputs gives exactly the same joint observation as
evaluating it with the original exogenous vector](goal). -/
-- @node: intervenedEval_nodeSet_mask
lemma intervenedEval_nodeSet_mask (M : EuclideanSCM kind dims)
    (S : Finset (Fin n)) (t : Intervention kind) (ht : ∀ i, t i = none → i ∈ S)
    (u : Exogenous kind dims) :
    intervenedEval M t (restrictLatentFamily (nodeSetLatentIndices M S) u) =
      intervenedEval M t u := by
  apply evalSteps_eq_of_unassigned_noise_eq
  · intro i hi k hk j
    exact nodeSet_mask_block M S i (ht i hi) k hk u j
  · intro i hi
    exact nodeSet_mask_noise M S i (ht i hi) u

variable {b : ℕ} {dims : Fin b → ℕ}

-- @node: counterexamplePrivateInput
/-- For [a structural causal model on the backdoor nodes](hyp:M),
[the private-input map for the covariate and outcome](goal) retains all latent
blocks and intrinsic noises read by either of those two nodes, setting the
other exogenous coordinates to zero. -/
def counterexamplePrivateInput (M : EuclideanSCM backdoorKind dims) :
    Exogenous backdoorKind dims → Exogenous backdoorKind dims :=
  restrictLatentFamily (nodeSetLatentIndices M {0, 2})

-- @node: counterexampleSelectionInput
/-- For [a structural causal model on the backdoor nodes](hyp:M),
[the treatment selection-input map](goal) retains all latent blocks and
intrinsic noises read by the treatment node, setting the other exogenous
coordinates to zero. -/
def counterexampleSelectionInput (M : EuclideanSCM backdoorKind dims) :
    Exogenous backdoorKind dims → Exogenous backdoorKind dims :=
  restrictLatentFamily (nodeSetLatentIndices M {1})

-- @node: counterexamplePrivateInput_measurable
/-- [The private-input map retaining the covariate and outcome inputs is
measurable](goal). -/
@[fun_prop] lemma counterexamplePrivateInput_measurable (M : EuclideanSCM backdoorKind dims) :
    Measurable (counterexamplePrivateInput M) := by
  unfold counterexamplePrivateInput
  fun_prop

-- @node: counterexampleSelectionInput_measurable
/-- [The map retaining the treatment's selection inputs is measurable](goal). -/
@[fun_prop] lemma counterexampleSelectionInput_measurable (M : EuclideanSCM backdoorKind dims) :
    Measurable (counterexampleSelectionInput M) := by
  unfold counterexampleSelectionInput
  fun_prop

-- @node: counterexample_private_inputs_independent
/-- If [the model has the backdoor causal graph](hyp:hgraph) and [its latent
blocks are independent](hyp:hind), then [the covariate-and-outcome private
input and the treatment selection input are independent under the latent
law](goal). -/
lemma counterexample_private_inputs_independent (M : EuclideanSCM backdoorKind dims)
    (hgraph : causalGraph M = backdoorGraph) (hind : LatentBlocksIndependent M) :
    IndepFun (counterexamplePrivateInput M) (counterexampleSelectionInput M) M.latentLaw := by
  apply nodeSet_private_inputs_independent M hind (congrArg Prod.snd hgraph)
  decide

/-- [The entire joint observation under either binary treatment intervention
is unchanged when the exogenous vector is replaced by the private input
retaining only the covariate and outcome inputs](goal). -/
-- @node: counterexample_potential_response_factorization
lemma counterexample_potential_response_factorization (M : EuclideanSCM backdoorKind dims)
    (t : Bool) (u : Exogenous backdoorKind dims) :
    intervenedEval M (binaryAssignment t) (counterexamplePrivateInput M u) =
      intervenedEval M (binaryAssignment t) u := by
  apply intervenedEval_nodeSet_mask
  intro i hi
  have hne : i ≠ 1 := by
    intro he
    subst i
    simp [binaryAssignment] at hi
  fin_cases i <;> simp_all

/-- If [the model has the backdoor causal graph](hyp:hgraph), then [each
coordinate of its observed covariate is unchanged when evaluation uses only
the covariate-and-outcome private input](goal). -/
-- @node: counterexample_covariate_private_factorization
lemma counterexample_covariate_private_factorization (M : EuclideanSCM backdoorKind dims)
    (hgraph : causalGraph M = backdoorGraph) (u : Exogenous backdoorKind dims)
    (j : Fin (valueDim (backdoorKind 0))) :
    (intervenedEval M (fun _ => none) (counterexamplePrivateInput M u)).ofLp ⟨0,j⟩ =
      (intervenedEval M (fun _ => none) u).ofLp ⟨0,j⟩ := by
  have hd : M.dag = backdoorDAG := congrArg Prod.fst hgraph
  apply evalSteps_eq_on_parent_closed_of_noise_eq M ({0} : Set (Fin 3)) _
    (fun _ => none) (counterexamplePrivateInput M u) u _ _ (3*3+3) 0 (by simp) j
  · intro i hi p hp
    have hi0 : i = 0 := Set.mem_singleton_iff.mp hi
    subst i
    have hlt : p < 0 := by
      simpa only [hd, backdoorDAG, backdoorEdges] using M.dag.mem_parents.mp hp
    exact (not_lt_of_ge (Fin.zero_le p) hlt).elim
  · intro i hi k hk l
    have hi0 : i = 0 := Set.mem_singleton_iff.mp hi
    subst i
    exact nodeSet_mask_block M {0,2} 0 (by simp) k hk u l
  · intro i hi
    have hi0 : i = 0 := Set.mem_singleton_iff.mp hi
    subst i
    exact nodeSet_mask_noise M {0,2} 0 (by simp) u

/-- [Each coordinate of a node in the completed observational simulation
equals the corresponding coordinate obtained by applying that node's
structural equation to the completed observation and the same exogenous
vector](goal). -/
-- @node: observationalEval_nodeValue_coordinate
lemma observationalEval_nodeValue_coordinate {n b : ℕ}
    {kind : Fin n → NodeKind} {dims : Fin b → ℕ} (M : EuclideanSCM kind dims)
    (i : Fin n) (u : Exogenous kind dims) (j : Fin (valueDim (kind i))) :
    (intervenedEval M (fun _ => none) u).ofLp ⟨i,j⟩ =
      (nodeValue M i (intervenedEval M (fun _ => none) u) u).ofLp j := by
  have he := evalSteps_coordinate_eq_intervenedEval M (fun _ => none) u i
    (M.dag.topoOrder i + 1) (by omega) j
  have hn : nodeValue M i (evalSteps M (fun _ => none) u (M.dag.topoOrder i)) u =
      nodeValue M i (intervenedEval M (fun _ => none) u) u := by
    unfold nodeValue
    rw [← counterexample_structuralInputRV_eq_visit]
    rfl
  calc
    _ = (evalSteps M (fun _ => none) u (M.dag.topoOrder i + 1)).ofLp ⟨i,j⟩ := he.symm
    _ = (nodeValue M i (evalSteps M (fun _ => none) u (M.dag.topoOrder i)) u).ofLp j := by
      simp only [evalSteps, WithLp.ofLp_toLp, if_pos rfl, Option.getD_none, ite_true]
    _ = _ := congrArg (fun z => z.ofLp j) hn

/-- For [a structural causal model on the backdoor nodes](hyp:M) and
[a pair of exogenous vectors](hyp:z), [the reconstructed scalar treatment](goal)
is the treatment node's structural value, using the observational simulation
from the first vector as its observed history and the second vector as its
exogenous input. -/
-- @node: counterexampleTreatmentFromPrivate
def counterexampleTreatmentFromPrivate (M : EuclideanSCM backdoorKind dims)
    (z : Exogenous backdoorKind dims × Exogenous backdoorKind dims) : ℝ :=
  (nodeValue M 1 (intervenedEval M (fun _ => none) z.1) z.2).ofLp ⟨0, by decide⟩

-- @node: counterexampleTreatmentFromPrivate_measurable
/-- [The scalar treatment reconstructed from a pair of exogenous vectors is
a measurable function of that pair](goal). -/
@[fun_prop] lemma counterexampleTreatmentFromPrivate_measurable
    (M : EuclideanSCM backdoorKind dims) : Measurable (counterexampleTreatmentFromPrivate M) := by
  unfold counterexampleTreatmentFromPrivate
  have hm : Measurable (fun z : Exogenous backdoorKind dims × Exogenous backdoorKind dims =>
      nodeValue M 1 (intervenedEval M (fun _ => none) z.1) z.2) := by
    have he : Measurable (intervenedEval M (fun _ => none)) :=
      evalSteps_measurable M (fun _ => none) (3*3+3)
    have hg : Measurable (fun z : Exogenous backdoorKind dims × Exogenous backdoorKind dims =>
        (intervenedEval M (fun _ => none) z.1, z.2)) :=
      (he.comp measurable_fst).prodMk measurable_snd
    exact Measurable.comp
      (g := fun z : Joint backdoorKind × Exogenous backdoorKind dims => nodeValue M 1 z.1 z.2)
      (f := fun z : Exogenous backdoorKind dims × Exogenous backdoorKind dims =>
        (intervenedEval M (fun _ => none) z.1, z.2))
      (nodeValue_measurable M 1) hg
  exact (show Measurable (fun z : L1Vec (valueDim (backdoorKind 1)) =>
    z.ofLp ⟨0, by decide⟩) by fun_prop).comp hm

-- @node: counterexample_treatment_private_factorization
/-- If [the model has the backdoor causal graph](hyp:hgraph), then [the
treatment reconstructed from the covariate-and-outcome private input and the
treatment selection input equals the observed scalar treatment for the
original exogenous vector](goal). -/
lemma counterexample_treatment_private_factorization (M : EuclideanSCM backdoorKind dims)
    (hgraph : causalGraph M = backdoorGraph) (u : Exogenous backdoorKind dims) :
    counterexampleTreatmentFromPrivate M (counterexamplePrivateInput M u,
      counterexampleSelectionInput M u) =
      (intervenedEval M (fun _ => none) u).ofLp ⟨1, ⟨0, by decide⟩⟩ := by
  have hd : M.dag = backdoorDAG := congrArg Prod.fst hgraph
  have hx : structuralInput M 1
      (intervenedEval M (fun _ => none) (counterexamplePrivateInput M u))
      (counterexampleSelectionInput M u) =
      structuralInput M 1 (intervenedEval M (fun _ => none) u) u := by
    apply WithLp.ofLp_injective
    funext c
    rcases c with ⟨p,k⟩ | ⟨a,k⟩
    · rcases p with ⟨p,hpMem⟩
      have hp : p = 0 := by
        have hlt : p < 1 := by
          simpa only [hd, backdoorDAG, backdoorEdges] using M.dag.mem_parents.mp hpMem
        exact Fin.ext (by simpa using hlt)
      change (intervenedEval M (fun _ => none) (counterexamplePrivateInput M u)).ofLp ⟨p,k⟩ =
        (intervenedEval M (fun _ => none) u).ofLp ⟨p,k⟩
      subst p
      exact counterexample_covariate_private_factorization M hgraph u k
    · exact nodeSet_mask_block M {1} 1 (by simp) a.val a.property u k
  have hg := nodeSet_mask_noise M {1} 1 (by simp) u
  change categoricalNoise 1 (counterexampleSelectionInput M u) = categoricalNoise 1 u at hg
  rw [observationalEval_nodeValue_coordinate M 1 u]
  unfold counterexampleTreatmentFromPrivate nodeValue
  simp only [Prod.fst, Prod.snd]
  rw [hx, hg]

/-- If [the observed treatment equals the selected arm's code, two for the
treated arm and one for the control arm](hyp:ht), then [the entire joint
observation under intervention on that arm equals the factual joint
observation for the same exogenous vector](goal). -/
-- @node: counterexample_consistency_on_selected_arm
lemma counterexample_consistency_on_selected_arm (M : EuclideanSCM backdoorKind dims)
    (t : Bool) (u : Exogenous backdoorKind dims)
    (ht : (intervenedEval M (fun _ => none) u).ofLp ⟨1, ⟨0, by decide⟩⟩ =
      (if t then 2 else 1 : ℝ)) :
    intervenedEval M (binaryAssignment t) u = intervenedEval M (fun _ => none) u := by
  apply intervenedEval_eq_of_factual_assignments
  intro i
  by_cases hi : i = 1
  · subst i
    right
    simp only [binaryAssignment, if_pos rfl]
    apply congrArg some
    apply WithLp.ofLp_injective
    funext j
    change Fin 1 at j
    have hj : j = ⟨0, by decide⟩ := Subsingleton.elim _ _
    subst j
    exact ht.symm
  · left
    simp [binaryAssignment, hi]

-- @node: counterexampleCovariate
/-- From [a joint observation of the backdoor nodes](hyp:v), [the scalar
covariate](goal) is the sole coordinate of the covariate node. -/
def counterexampleCovariate (v : Joint backdoorKind) : ℝ := v.ofLp ⟨0, ⟨0, by decide⟩⟩

-- @node: counterexampleCovariate_measurable
/-- [Extracting the scalar covariate from a joint observation is
measurable](goal). -/
@[fun_prop] lemma counterexampleCovariate_measurable : Measurable counterexampleCovariate := by
  unfold counterexampleCovariate
  fun_prop

/-- For [a structural causal model on the backdoor nodes](hyp:M) and
[a scalar covariate paired with an exogenous vector](hyp:z), [the scalar
treatment function](goal) applies the treatment node's structural equation
to a history containing that covariate and zeros at the other nodes, using
the paired exogenous vector. -/
-- @node: counterexampleScalarTreatment
def counterexampleScalarTreatment (M : EuclideanSCM backdoorKind dims)
    (z : ℝ × Exogenous backdoorKind dims) : ℝ :=
  (nodeValue M 1 (WithLp.toLp 1 (fun k => if k.1 = 0 then z.1 else 0)) z.2).ofLp ⟨0, by decide⟩

-- @node: counterexampleScalarTreatment_measurable
/-- [The scalar treatment function is measurable in the covariate and
exogenous vector](goal). -/
@[fun_prop] lemma counterexampleScalarTreatment_measurable
    (M : EuclideanSCM backdoorKind dims) : Measurable (counterexampleScalarTreatment M) := by
  unfold counterexampleScalarTreatment
  have hh : Measurable (fun z : ℝ × Exogenous backdoorKind dims =>
      (WithLp.toLp 1 (fun k : (Σ i : Fin 3, Fin (valueDim (backdoorKind i))) => if k.1 = 0 then z.1 else 0), z.2)) := by
    apply Measurable.prodMk
    · apply scm_toLp_measurable.comp
      apply measurable_pi_lambda
      intro k
      split_ifs <;> fun_prop
    · exact measurable_snd
  have hm := Measurable.comp
    (g := fun z : Joint backdoorKind × Exogenous backdoorKind dims => nodeValue M 1 z.1 z.2)
    (f := fun z : ℝ × Exogenous backdoorKind dims =>
      (WithLp.toLp 1 (fun k => if k.1 = 0 then z.1 else 0), z.2))
    (nodeValue_measurable M 1) hh
  exact (show Measurable (fun z : L1Vec (valueDim (backdoorKind 1)) =>
    z.ofLp ⟨0, by decide⟩) by fun_prop).comp hm

/-- If [the model has the backdoor causal graph](hyp:hgraph), then [the
treatment structural value at any joint history equals the scalar treatment
function evaluated at that history's covariate and the same exogenous
vector](goal). -/
-- @node: counterexample_treatment_depends_only_on_covariate
lemma counterexample_treatment_depends_only_on_covariate (M : EuclideanSCM backdoorKind dims)
    (hgraph : causalGraph M = backdoorGraph) (v : Joint backdoorKind)
    (u : Exogenous backdoorKind dims) :
    (nodeValue M 1 v u).ofLp ⟨0, by decide⟩ =
      counterexampleScalarTreatment M (counterexampleCovariate v, u) := by
  have hd : M.dag = backdoorDAG := congrArg Prod.fst hgraph
  have hx : structuralInput M 1 v u = structuralInput M 1
      (WithLp.toLp 1 (fun k => if k.1 = 0 then counterexampleCovariate v else 0)) u := by
    apply WithLp.ofLp_injective
    funext c
    rcases c with ⟨⟨p,hpMem⟩,k⟩ | ⟨a,k⟩
    · have hp : p = 0 := by
        have hlt : p < 1 := by
          simpa only [hd, backdoorDAG, backdoorEdges] using M.dag.mem_parents.mp hpMem
        exact Fin.ext (by simpa using hlt)
      subst p
      change v.ofLp ⟨0,k⟩ =
        (WithLp.toLp 1 (fun c => if c.1 = 0 then counterexampleCovariate v else 0) :
          Joint backdoorKind).ofLp ⟨0,k⟩
      change Fin 1 at k
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      rfl
    · rfl
  unfold counterexampleScalarTreatment nodeValue
  simp only [Prod.fst, Prod.snd]
  rw [← hx]

/-- If [the model has the backdoor causal graph](hyp:hgraph), then [the
potential outcome computed from the covariate-and-outcome private input,
divided by the chosen arm's covariate propensity when the reconstructed
treatment selects that arm and set to zero otherwise, equals the observed
arm score](goal). -/
-- @node: counterexample_selected_score_private_factorization
lemma counterexample_selected_score_private_factorization
    (M : EuclideanSCM backdoorKind dims) (hgraph : causalGraph M = backdoorGraph)
    (t : Bool) (u : Exogenous backdoorKind dims) :
    (if counterexampleTreatmentFromPrivate M
        (counterexamplePrivateInput M u, counterexampleSelectionInput M u) =
          (if t then 2 else 1 : ℝ) then
      backdoorOutcome (intervenedEval M (binaryAssignment t) (counterexamplePrivateInput M u)) /
        (if t then counterexampleTrueTreatmentProbability
          (counterexampleCovariate (intervenedEval M (fun _ => none) (counterexamplePrivateInput M u)))
        else 1 - counterexampleTrueTreatmentProbability
          (counterexampleCovariate (intervenedEval M (fun _ => none) (counterexamplePrivateInput M u))))
      else 0) = counterexampleArmScore t (intervenedEval M (fun _ => none) u) := by
  rw [counterexample_treatment_private_factorization M hgraph u,
    counterexample_potential_response_factorization]
  have hx := counterexample_covariate_private_factorization M hgraph u ⟨0, by decide⟩
  change counterexampleCovariate (intervenedEval M (fun _ => none) (counterexamplePrivateInput M u)) =
    counterexampleCovariate (intervenedEval M (fun _ => none) u) at hx
  rw [hx]
  dsimp only [counterexampleArmScore]
  by_cases ht : (intervenedEval M (fun _ => none) u).ofLp ⟨1, ⟨0, by decide⟩⟩ =
      (if t then 2 else 1 : ℝ)
  · simp only [ht, if_true]
    rw [counterexample_consistency_on_selected_arm M t u ht]
    rfl
  · simp only [ht, if_false]

/-- If [the model has the backdoor causal graph](hyp:hgraph), [its latent
blocks are independent](hyp:hind), [its observational law equals the witness
model's law](hyp:hobs), and [for each arm, integrating the reconstructed
selection indicator over the treatment selection-input law gives that arm's
covariate propensity for almost every covariate-and-outcome private
input](hyp:hcal), then [the model's average treatment effect equals the
observational expectation of the adjustment score](goal). -/
-- @node: counterexample_adjustment_of_private_calibration
lemma counterexample_adjustment_of_private_calibration
    (M : EuclideanSCM backdoorKind dims) (hgraph : causalGraph M = backdoorGraph)
    (hind : LatentBlocksIndependent M)
    (hobs : observationalLaw M = observationalLaw counterexampleTrueSCM.toEuclideanSCM)
    (hcal : ∀ t : Bool, ∀ᵐ v ∂M.latentLaw.map (counterexamplePrivateInput M),
      (∫ g, (if counterexampleTreatmentFromPrivate M (v,g) = (if t then 2 else 1 : ℝ)
        then (1 : ℝ) else 0) ∂M.latentLaw.map (counterexampleSelectionInput M)) =
      (if t then counterexampleTrueTreatmentProbability
        (counterexampleCovariate (intervenedEval M (fun _ => none) v))
      else 1 - counterexampleTrueTreatmentProbability
        (counterexampleCovariate (intervenedEval M (fun _ => none) v)))) :
    backdoorATE M = ∫ v, counterexampleAdjustmentScore v ∂observationalLaw M := by
  have hmean (t : Bool) :
      Integrable (fun u => backdoorOutcome (intervenedEval M (binaryAssignment t) u)) M.latentLaw ∧
      (∫ u, backdoorOutcome (intervenedEval M (binaryAssignment t) u) ∂M.latentLaw) =
        (if t then 4/5 else 1/6 : ℝ) := by
    let V := counterexamplePrivateInput M
    let G := counterexampleSelectionInput M
    let S : Exogenous backdoorKind dims × Exogenous backdoorKind dims → Prop :=
      fun z => counterexampleTreatmentFromPrivate M z = (if t then 2 else 1 : ℝ)
    let Y : Exogenous backdoorKind dims → ℝ := fun v =>
      backdoorOutcome (intervenedEval M (binaryAssignment t) v)
    let p : Exogenous backdoorKind dims → ℝ := fun v =>
      if t then counterexampleTrueTreatmentProbability
        (counterexampleCovariate (intervenedEval M (fun _ => none) v))
      else 1 - counterexampleTrueTreatmentProbability
        (counterexampleCovariate (intervenedEval M (fun _ => none) v))
    have hS : MeasurableSet {z | S z} :=
      (counterexampleTreatmentFromPrivate_measurable M) (measurableSet_singleton _)
    have hY : Measurable Y := by
      dsimp only [Y]
      exact (show Measurable backdoorOutcome by fun_prop [backdoorOutcome]).comp
        (evalSteps_measurable M (binaryAssignment t) (3*3+3))
    have hp : Measurable p := by
      dsimp only [p]
      have hx : Measurable (fun v => counterexampleCovariate (intervenedEval M (fun _ => none) v)) :=
        counterexampleCovariate_measurable.comp (evalSteps_measurable M (fun _ => none) (3*3+3))
      have hprob := counterexampleTrueTreatmentProbability_measurable.comp hx
      cases t
      · exact measurable_const.sub hprob
      · exact hprob
    have hpos : ∀ᵐ v ∂M.latentLaw.map V, p v ≠ 0 := by
      apply ae_of_all
      intro v
      have hh := counterexampleTrueTreatmentProbability_overlap
        (counterexampleCovariate (intervenedEval M (fun _ => none) v))
      cases t
      · exact ne_of_gt hh.2
      · exact ne_of_gt hh.1
    obtain ⟨hi, he⟩ := counterexample_selected_response_identification M hobs t V G
      (counterexamplePrivateInput_measurable M) (counterexampleSelectionInput_measurable M)
      (counterexample_private_inputs_independent M hgraph hind) S hS Y p hY hp hpos (hcal t)
      (ae_of_all _ (counterexample_selected_score_private_factorization M hgraph t))
    have heq : (fun u => Y (V u)) =
        (fun u => backdoorOutcome (intervenedEval M (binaryAssignment t) u)) := by
      funext u
      exact congrArg backdoorOutcome (counterexample_potential_response_factorization M t u)
    rw [heq] at hi he
    exact ⟨hi, he⟩
  have h1 := hmean true
  have h0 := hmean false
  calc
    backdoorATE M = (∫ u, backdoorOutcome (intervenedEval M (binaryAssignment true) u) ∂M.latentLaw) -
        ∫ u, backdoorOutcome (intervenedEval M (binaryAssignment false) u) ∂M.latentLaw :=
      integral_sub h1.1 h0.1
    _ = 19/30 := by rw [h1.2, h0.2]; norm_num
    _ = _ := (counterexample_adjustment_integral_of_observational_eq M hobs).symm

end
end Papers.TbsNeuralCausalPi
