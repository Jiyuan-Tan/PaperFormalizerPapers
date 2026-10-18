module
public import Papers.TbsNeuralCausalPi.Setup.Networks
/-! # Admissible structural inputs and canonical evaluation congruence -/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false
set_option linter.unusedVariables false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

-- @node: observedValueEmbedding_categorical_label
/-- If [the node type is categorical with the given number of categories](hyp:hk),
[every coordinate of an embedded observed value equals the same integer label
between one and that number of categories](goal). -/
lemma observedValueEmbedding_categorical_label {κ : NodeKind} {k : ℕ}
    (hk : κ = .inr k) (y : ObservedValue κ) :
    ∃ label : Fin k, ∀ j, (observedValueEmbedding κ y).ofLp j = (label.val + 1 : ℕ) := by
  subst κ
  exact ⟨y, fun _ => rfl⟩

-- @node: evalSteps_intervention_categorical_label
/-- Under [an admissible intervention](hyp:ht), if [the node is categorical with
the given number of categories](hyp:hk) and [its position in the topological order
is earlier than the number of completed evaluation steps](hyp:hr), [all its
evaluated coordinates equal a single integer label between one and that number
of categories](goal). -/
lemma evalSteps_intervention_categorical_label (M : EuclideanSCM kind dims)
    (t : Intervention kind) (ht : AdmissibleIntervention kind t)
    (u : Exogenous kind dims) (i : Fin n) (k : ℕ) (hk : kind i = .inr k)
    (r : ℕ) (hr : M.dag.topoOrder i < r) :
    ∃ label : Fin k, ∀ j,
      (evalSteps M t u r).ofLp ⟨i,j⟩ = (label.val + 1 : ℕ) := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hi : M.dag.topoOrder i = r
    · cases he : t i with
      | some v =>
        have hv := ht i v he
        split at hv
        · rename_i h
          simp [hk] at h
        · rename_i k' h
          have heq : k' = k := Sum.inr.inj (h.symm.trans hk)
          subst k'
          obtain ⟨label, hv⟩ := hv
          exact ⟨label, fun j => by simpa [evalSteps, hi, he] using hv j⟩
      | none =>
        obtain ⟨label, hv⟩ := observedValueEmbedding_categorical_label hk
          (M.f i (structuralInput M i (evalSteps M t u r) u) (categoricalNoise i u))
        refine ⟨label, ?_⟩
        intro j
        simp only [evalSteps, WithLp.ofLp_toLp, hi, if_true, he, Option.getD_none]
        have hn := observedValueEmbedding_eq (kind i)
          (M.f i (structuralInput M i (evalSteps M t u r) u) (categoricalNoise i u))
        change (nodeValue M i (evalSteps M t u r) u).ofLp j = _
        rw [show nodeValue M i (evalSteps M t u r) u = _ from hn.symm]
        exact hv j
    · obtain ⟨label, hv⟩ := ih (by omega)
      exact ⟨label, fun j => by simpa [evalSteps, hi] using hv j⟩

-- @node: evalSteps_structuralInput_mem_domain
/-- Under [an admissible intervention](hyp:ht), if [the node's position in the
topological order equals the number of completed evaluation steps](hyp:hr),
[the structural input assembled for that node belongs to its admissible domain](goal). -/
lemma evalSteps_structuralInput_mem_domain (M : EuclideanSCM kind dims)
    (t : Intervention kind) (ht : AdmissibleIntervention kind t)
    (u : Exogenous kind dims) (i : Fin n) (r : ℕ)
    (hr : M.dag.topoOrder i = r) :
    structuralInput M i (evalSteps M t u r) u ∈ M.domain i none := by
  refine ⟨?_, Set.mem_univ _⟩
  intro p k hk
  have hp : M.dag.topoOrder p.val < r := by
    rw [← hr]
    exact M.dag.topoOrder_lt _ _ (M.dag.mem_parents.mp p.property)
  exact evalSteps_intervention_categorical_label M t ht u p.val k hk r hp

-- @node: canonical_nodeValue_eq_of_weights_eq
/-- If [two canonical models have equal mechanism weights at the structural input
assembled by the second model for a given node, joint value, and exogenous
input](hyp:hf), [their realized values at that node agree for those same joint and
exogenous inputs](goal). -/
lemma canonical_nodeValue_eq_of_weights_eq
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)} (M N : CanonicalSCM kind dims dag G C)
    (i : Fin n) (v : Joint kind) (u : Exogenous kind dims)
    (hf : M.f i (structuralInput N.toEuclideanSCM i v u) =
      N.f i (structuralInput N.toEuclideanSCM i v u)) :
    nodeValue M.toEuclideanSCM i v u = nodeValue N.toEuclideanSCM i v u := by
  have hm : canonicalMechanism M i (structuralInput N.toEuclideanSCM i v u)
      (categoricalNoise i u) =
      canonicalMechanism N i (structuralInput N.toEuclideanSCM i v u)
        (categoricalNoise i u) := by
    unfold canonicalMechanism
    simp only [hf]
  have heM : nodeValue M.toEuclideanSCM i v u =
      observedValueEmbedding (kind i)
        (M.toEuclideanSCM.f i (structuralInput M.toEuclideanSCM i v u) (categoricalNoise i u)) :=
    (observedValueEmbedding_eq _ _).symm
  have heN : nodeValue N.toEuclideanSCM i v u =
      observedValueEmbedding (kind i)
        (N.toEuclideanSCM.f i (structuralInput N.toEuclideanSCM i v u) (categoricalNoise i u)) :=
    (observedValueEmbedding_eq _ _).symm
  rw [heM, heN]
  convert congrArg (observedValueEmbedding (kind i)) hm using 1
  · congr 2
    apply WithLp.ofLp_injective
    funext j
    rcases j with ⟨p,j⟩ | ⟨k,j⟩ <;> rfl
  · rfl

-- @node: canonical_evalSteps_eq_of_weights_eq
/-- If [two canonical models have equal mechanism weights at every node visited
before the specified step, evaluated at the structural inputs along the second
model's trajectory](hyp:hf), [their joint evaluations after that many steps agree
under the same intervention and exogenous input](goal). -/
lemma canonical_evalSteps_eq_of_weights_eq
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)} (M N : CanonicalSCM kind dims dag G C)
    (t : Intervention kind) (u : Exogenous kind dims) (r : ℕ)
    (hf : ∀ k < r, ∀ i, dag.topoOrder i = k →
      M.f i (structuralInput N.toEuclideanSCM i (evalSteps N.toEuclideanSCM t u k) u) =
      N.f i (structuralInput N.toEuclideanSCM i (evalSteps N.toEuclideanSCM t u k) u)) :
    evalSteps M.toEuclideanSCM t u r = evalSteps N.toEuclideanSCM t u r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have he := ih (fun k hk => hf k (by omega))
    apply WithLp.ofLp_injective
    funext ⟨i,j⟩
    simp only [evalSteps, WithLp.ofLp_toLp]
    change (if dag.topoOrder i = r then _ else _) =
      (if dag.topoOrder i = r then _ else _)
    rw [he]
    by_cases hi : dag.topoOrder i = r
    · simp only [hi, if_true]
      rw [canonical_nodeValue_eq_of_weights_eq M N i _ u (hf r (by omega) i hi)]
    · simp only [hi, if_false]

end
end Papers.TbsNeuralCausalPi
