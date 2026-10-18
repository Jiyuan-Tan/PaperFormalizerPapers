module
public import Papers.TbsNeuralCausalPi.Helpers.DescendantNoise
/-! # Independence of a structural history and the next node's private noise

Before a node's topological slot is visited, evaluation uses none of its private
inputs. Masking those inputs therefore leaves the whole current history unchanged.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- For [a node](hyp:i) and [the family of latent-block incidence sets](hyp:C),
[the node's private noise indices](goal) consist of [the non-Gumbel blocks incident
to that node](step:1) and [that node's own intrinsic noise block](step:2). -/
-- @node: nodeLatentIndices
def nodeLatentIndices (i : Fin n) : Finset (Fin b ⊕ Fin n) :=
  Finset.univ.filter (fun j => match j with
    | .inl k => k ∈ canonicalIncidence C i
    | .inr k => k = i)

/-- If [the confounding graph has no hidden confounding](hyp:hnoconf) and
[the evaluation stage is no later than the node's topological slot](hyp:hr), then
[zeroing that node's private noise blocks leaves the evaluation history unchanged](goal).

This holds for fixed interventions as well as factual evaluation. -/
-- @node: evalSteps_restrict_complement_node_noise
lemma evalSteps_restrict_complement_node_noise
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (i : Fin n) (t : Intervention kind) (u : Exogenous kind dims)
    (r : ℕ) (hr : r ≤ dag.topoOrder i) :
    evalSteps M.toEuclideanSCM t u r =
      evalSteps M.toEuclideanSCM t
        (restrictLatentFamily (nodeLatentIndices (C := C) i)ᶜ u) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hp := ih (by omega)
    apply WithLp.ofLp_injective
    funext ⟨j,k⟩
    simp only [evalSteps, WithLp.ofLp_toLp]
    by_cases hj : dag.topoOrder j = r
    · have hji : j ≠ i := by intro he; subst j; omega
      have hx : structuralInput M.toEuclideanSCM j
          (evalSteps M.toEuclideanSCM t u r) u =
          structuralInput M.toEuclideanSCM j
            (evalSteps M.toEuclideanSCM t
              (restrictLatentFamily (nodeLatentIndices (C := C) i)ᶜ u) r)
            (restrictLatentFamily (nodeLatentIndices (C := C) i)ᶜ u) := by
        rw [hp]
        apply WithLp.ofLp_injective
        funext c
        rcases c with ⟨p,l⟩ | ⟨a,l⟩
        · rfl
        · have ha : a.val ∉ canonicalIncidence C i := by
            intro hai
            exact hji (canonicalIncidence_node_unique M hnoconf a.property hai)
          change u.ofLp (.inl ⟨a.val,l⟩) =
            if Sum.inl a.val ∈ (nodeLatentIndices (C := C) i)ᶜ then
              u.ofLp (.inl ⟨a.val,l⟩) else 0
          have hmem : Sum.inl a.val ∉ nodeLatentIndices (C := C) i := by
            simpa only [nodeLatentIndices, Finset.mem_filter, Finset.mem_univ, true_and] using ha
          simp only [Finset.mem_compl, hmem, not_false_eq_true, if_true]
      have hg : categoricalNoise j u =
          categoricalNoise j (restrictLatentFamily (nodeLatentIndices (C := C) i)ᶜ u) := by
        apply WithLp.ofLp_injective
        funext l
        change u.ofLp (.inr ⟨j,l⟩) =
          if Sum.inr j ∈ (nodeLatentIndices (C := C) i)ᶜ then
            u.ofLp (.inr ⟨j,l⟩) else 0
        have hmem : Sum.inr j ∉ nodeLatentIndices (C := C) i := by
          simpa only [nodeLatentIndices, Finset.mem_filter, Finset.mem_univ, true_and] using hji
        simp only [Finset.mem_compl, hmem, not_false_eq_true, if_true]
      have hn : nodeValue M.toEuclideanSCM j (evalSteps M.toEuclideanSCM t u r) u =
          nodeValue M.toEuclideanSCM j
            (evalSteps M.toEuclideanSCM t
              (restrictLatentFamily (nodeLatentIndices (C := C) i)ᶜ u) r)
            (restrictLatentFamily (nodeLatentIndices (C := C) i)ᶜ u) := by
        unfold nodeValue
        rw [hx, hg]
      change (if dag.topoOrder j = r then _ else _) =
        (if dag.topoOrder j = r then _ else _)
      simp only [hj, if_true]
      rw [hn]
    · change (if dag.topoOrder j = r then _ else _) =
        (if dag.topoOrder j = r then _ else _)
      simp only [hj, if_false]
      exact congrArg (fun v : Joint kind => v.ofLp ⟨j,k⟩) hp

/-- If [the confounding graph has no hidden confounding](hyp:hnoconf),
[the model's latent blocks are independent](hyp:hind), and [the evaluation stage is
no later than the node's topological slot](hyp:hr), then [the evaluation history and
the node's private input vector are independent under the model's latent law](goal). -/
-- @node: evalSteps_indep_node_private_noise
lemma evalSteps_indep_node_private_noise
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (i : Fin n) (t : Intervention kind) (r : ℕ) (hr : r ≤ dag.topoOrder i) :
    IndepFun (fun u => evalSteps M.toEuclideanSCM t u r)
      (restrictLatentFamily (nodeLatentIndices (C := C) i)) M.latentLaw := by
  let S := nodeLatentIndices (C := C) i
  let H := fun u => evalSteps M.toEuclideanSCM t u r
  have hm : Measurable H := by
    fun_prop
  have he : H ∘ restrictLatentFamily Sᶜ = H := by
    funext u
    exact (evalSteps_restrict_complement_node_noise M hnoconf i t u r hr).symm
  have h := (restrictLatentFamily_indepFun M.toEuclideanSCM hind Sᶜ S
    disjoint_compl_left).comp hm measurable_id
  change IndepFun H (restrictLatentFamily S) M.toEuclideanSCM.latentLaw
  simpa only [he, Function.id_comp] using h

/-- If [the confounding graph has no hidden confounding](hyp:hnoconf),
[the model's latent blocks are independent](hyp:hind), and [the evaluation stage is
no later than the node's topological slot](hyp:hr), then [the joint law of the evaluation
history and the node's private inputs equals the product of their marginal laws](goal). -/
-- @node: evalSteps_node_private_noise_joint_law
lemma evalSteps_node_private_noise_joint_law
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (i : Fin n) (t : Intervention kind) (r : ℕ) (hr : r ≤ dag.topoOrder i) :
    M.latentLaw.map (fun u => (evalSteps M.toEuclideanSCM t u r,
      restrictLatentFamily (nodeLatentIndices (C := C) i) u)) =
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u r)).prod
        (M.latentLaw.map (restrictLatentFamily (nodeLatentIndices (C := C) i))) := by
  let := M.latentLaw_probability
  exact (evalSteps_indep_node_private_noise M hnoconf hind i t r hr).map_prod_eq_prod_map_map
    (evalSteps_measurable M.toEuclideanSCM t r).aemeasurable
    (restrictLatentFamily_measurable _).aemeasurable


/-- [A node's value at a fixed history is unchanged when every noise block outside
that node's private input set is replaced by zero](goal). -/
-- @node: nodeValue_restrict_node_noise
lemma nodeValue_restrict_node_noise
    (M : CanonicalSCM kind dims dag G C) (i : Fin n)
    (v : Joint kind) (u : Exogenous kind dims) :
    nodeValue M.toEuclideanSCM i v u = nodeValue M.toEuclideanSCM i v
      (restrictLatentFamily (nodeLatentIndices (C := C) i) u) := by
  have hx : structuralInput M.toEuclideanSCM i v u =
      structuralInput M.toEuclideanSCM i v
        (restrictLatentFamily (nodeLatentIndices (C := C) i) u) := by
    apply WithLp.ofLp_injective
    funext c
    rcases c with ⟨p,j⟩ | ⟨a,j⟩
    · rfl
    · change u.ofLp (.inl ⟨a.val,j⟩) =
        if Sum.inl a.val ∈ nodeLatentIndices (C := C) i then
          u.ofLp (.inl ⟨a.val,j⟩) else 0
      have ha : Sum.inl a.val ∈ nodeLatentIndices (C := C) i := by
        simp only [nodeLatentIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        exact a.property
      simp only [ha, if_true]
  have hg : categoricalNoise i u =
      categoricalNoise i (restrictLatentFamily (nodeLatentIndices (C := C) i) u) := by
    apply WithLp.ofLp_injective
    funext j
    change u.ofLp (.inr ⟨i,j⟩) =
      if Sum.inr i ∈ nodeLatentIndices (C := C) i then u.ofLp (.inr ⟨i,j⟩) else 0
    have hi : Sum.inr i ∈ nodeLatentIndices (C := C) i := by
      simp only [nodeLatentIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [hi, if_true]
  unfold nodeValue
  rw [hx, hg]

/-- For [a structural causal model](hyp:M), [a node to update](hyp:i),
[an intervention](hyp:t), and [a pair consisting of a history and an exogenous input vector](hyp:z),
[the updated history](goal) replaces that node's block by its intervention value when present,
or otherwise by its structural value, and retains all other coordinate blocks. -/
-- @node: nodeHistoryUpdate
def nodeHistoryUpdate (M : EuclideanSCM kind dims) (i : Fin n)
    (t : Intervention kind) (z : Joint kind × Exogenous kind dims) : Joint kind :=
  WithLp.toLp 1 (fun ⟨j,k⟩ => if h : j = i then
    ((t i).getD (nodeValue M i z.1 z.2)).ofLp
      (Fin.cast (congrArg (fun j => valueDim (kind j)) h) k) else z.1.ofLp ⟨j,k⟩)

-- @node: nodeHistoryUpdate_measurable
/-- [The map that updates a single node in a structural causal model under a fixed
intervention is measurable as a function of the history and exogenous inputs](goal). -/
@[fun_prop] lemma nodeHistoryUpdate_measurable
    (M : EuclideanSCM kind dims) (i : Fin n) (t : Intervention kind) :
    Measurable (nodeHistoryUpdate M i t) := by
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  rintro ⟨j,k⟩
  dsimp [nodeHistoryUpdate]
  by_cases h : j = i
  · simp only [h, ↓reduceDIte]
    cases he : t i with
    | none =>
      simp only [Option.getD_none]
      exact (measurable_pi_apply _).comp
        (scm_ofLp_measurable.comp (nodeValue_measurable M i))
    | some w => simp only [Option.getD_some]; fun_prop
  · simp only [h, ↓reduceDIte]
    fun_prop

/-- [The evaluation history immediately after a node's topological slot equals the
single-node update of the preceding history using only that node's private inputs](goal). -/
-- @node: evalSteps_succ_eq_nodeHistoryUpdate
lemma evalSteps_succ_eq_nodeHistoryUpdate
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (t : Intervention kind)
    (u : Exogenous kind dims) :
    evalSteps M.toEuclideanSCM t u (dag.topoOrder i + 1) =
      nodeHistoryUpdate M.toEuclideanSCM i t
        (evalSteps M.toEuclideanSCM t u (dag.topoOrder i),
          restrictLatentFamily (nodeLatentIndices (C := C) i) u) := by
  apply WithLp.ofLp_injective
  funext ⟨j,k⟩
  by_cases h : j = i
  · subst j
    simp only [evalSteps, nodeHistoryUpdate, WithLp.ofLp_toLp, ↓reduceDIte]
    rw [nodeValue_restrict_node_noise M i]
    simp only [show M.toEuclideanSCM.dag.topoOrder i = dag.topoOrder i from rfl,
      if_true, Fin.cast_eq_self]
  · have hr : dag.topoOrder j ≠ dag.topoOrder i :=
      fun he => h (dag.topoOrder_injective he)
    change (if dag.topoOrder j = dag.topoOrder i then _ else _) = _
    simp only [hr, if_false, nodeHistoryUpdate, WithLp.ofLp_toLp, h, ↓reduceDIte]

/-- If [the confounding graph has no hidden confounding](hyp:hnoconf) and
[the model's latent blocks are independent](hyp:hind), then [the history law immediately
after a node's slot is the distribution obtained by applying the single-node update
to the product of the preceding history law and that node's private-input law](goal). -/
-- @node: evalSteps_succ_law_eq_product_update
lemma evalSteps_succ_law_eq_product_update
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (i : Fin n) (t : Intervention kind) :
    M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (dag.topoOrder i + 1)) =
      ((M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u (dag.topoOrder i))).prod
        (M.latentLaw.map (restrictLatentFamily (nodeLatentIndices (C := C) i)))).map
        (nodeHistoryUpdate M.toEuclideanSCM i t) := by
  rw [← evalSteps_node_private_noise_joint_law M hnoconf hind i t _ le_rfl,
    Measure.map_map (nodeHistoryUpdate_measurable M.toEuclideanSCM i t)
      ((evalSteps_measurable M.toEuclideanSCM t _).prodMk
        (restrictLatentFamily_measurable _))]
  congr 1
  funext u
  exact evalSteps_succ_eq_nodeHistoryUpdate M i t u

end
end Papers.TbsNeuralCausalPi
