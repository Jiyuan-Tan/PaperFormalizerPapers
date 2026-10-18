module
public import Papers.TbsNeuralCausalPi.Helpers.GeneralCategoricalTransition
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalRegrouping
/-! # Measurable mechanisms for canonical regrouping

Normalized propensities are measurable on their actual input domains by the
categorical generation law. Extending them off those domains gives total
measurable canonical mechanisms without regularity assumptions on raw weights.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
noncomputable section

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

-- @node: admissibleStructuralInputs_measurableSet
/-- [The admissible structural inputs for a node, with the given directed graph and latent-block incidence, form a measurable set](goal). -/
lemma admissibleStructuralInputs_measurableSet
    (dag : Causalean.Graph.DAG (Fin n)) (inc : Fin n → Finset (Fin b)) (i : Fin n) :
    MeasurableSet (admissibleStructuralInputs kind dims dag inc i) := by
  unfold admissibleStructuralInputs
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  repeat' first | apply MeasurableSet.iInter | apply MeasurableSet.iUnion | intro
  exact measurableSet_eq_fun (by fun_prop) measurable_const

-- @node: EuclideanSCM.domain_measurableSet
/-- [Each node's structural input domain in a Euclidean structural causal model is measurable](goal). -/
lemma EuclideanSCM.domain_measurableSet (M : EuclideanSCM kind dims) (i : Fin n) :
    MeasurableSet (M.domain i) := by
  simpa only [EuclideanSCM.domain, structuralInputDomain, Set.inter_univ] using
    admissibleStructuralInputs_measurableSet M.dag M.incidence i

-- @node: EuclideanSCM.continuousMap_measurable
/-- [The vector-valued mechanism obtained by fixing a node's intrinsic noise to zero and retaining its continuous output, or returning zero at a categorical node, is measurable](goal). -/
@[fun_prop] lemma EuclideanSCM.continuousMap_measurable
    (M : EuclideanSCM kind dims) (i : Fin n) : Measurable (M.continuousMap i) := by
  first | fun_prop | skip
  have hc : Measurable (fun y : ObservedValue (kind i) =>
      show L1Vec (outputDim (kind i)) from match h : kind i with
      | .inl d => WithLp.toLp 1 (fun j => (cast (congrArg ObservedValue h) y).ofLp j)
      | .inr _ => 0) := by
    generalize hv : kind i = v
    cases v
    · exact measurable_id
    · exact measurable_const
  exact hc.comp ((M.structuralMeasurable i).comp
    (measurable_id.prodMk measurable_const))

/-- If [the model's categorical mechanisms use Gumbel argmax generation with the given weights](hyp:hcat) and [the selected node is categorical with k alternatives](hyp:hi), then [there is a measurable function on the full structural input space that agrees with the weights divided by their total at every input in the node's domain](goal). -/
-- @node: exists_measurable_normalized_propensity
lemma exists_measurable_normalized_propensity
    (M : EuclideanSCM kind dims) (p : MechanismWeights M)
    (hcat : CategoricalGumbelArgmax M p) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) :
    ∃ w : StructuralInput kind dims M.dag M.incidence i → L1Vec (outputDim (kind i)),
      Measurable w ∧ ∀ x ∈ M.domain i,
        w x = WithLp.toLp 1 (fun j => (p i x).ofLp j / ∑ l, (p i x).ofLp l) := by
  classical
  let w : M.domain i → L1Vec (outputDim (kind i)) := fun x =>
    WithLp.toLp 1 (fun j => (p i x.val).ofLp j / ∑ l, (p i x.val).ofLp l)
  have hw : Measurable w := by
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    intro j
    change Measurable (fun x : M.domain i =>
      (p i x.val).ofLp j / ∑ l, (p i x.val).ofLp l)
    have h := categorical_normalized_coordinate_measurable M p hcat i k hi
      (Fin.cast (congrArg outputDim hi) j)
    convert h using 1
    funext x
    exact congrArg (fun q : Fin (outputDim (kind i)) =>
      (p i x.val).ofLp q / ∑ l, (p i x.val).ofLp l) (Fin.ext rfl)
  let W : StructuralInput kind dims M.dag M.incidence i → L1Vec (outputDim (kind i)) :=
    fun x => if hx : x ∈ M.domain i then w ⟨x,hx⟩ else 0
  refine ⟨W, hw.dite measurable_const (M.domain_measurableSet i), ?_⟩
  intro x hx
  simp only [W, dif_pos hx, w]

/-- Suppose [the original categorical mechanisms use Gumbel argmax generation with the given weights](hyp:hcat), and [continuous linear maps project each canonical structural input space to the corresponding original input space](hyp:pi), [sending admissible canonical inputs into the original domains](hyp:hpi). Then [there exist total measurable vector-valued mechanisms that equal the original continuous mechanisms after projection at continuous nodes, equal the normalized original weights after projection at admissible categorical inputs, and take values in the probability simplex at those categorical inputs](goal). -/
-- @node: exists_canonical_regrouped_mechanisms
lemma exists_canonical_regrouped_mechanisms
    (M : EuclideanSCM kind dims) (p : MechanismWeights M)
    (hcat : CategoricalGumbelArgmax M p) {b' : ℕ}
    (dims' : Fin b' → ℕ) (C : Fin b' → Set (Fin n))
    (pi : ∀ i, StructuralInput kind dims' M.dag (canonicalIncidence C) i →L[ℝ]
      StructuralInput kind dims M.dag M.incidence i)
    (hpi : ∀ i, Set.MapsTo (pi i)
      (admissibleStructuralInputs kind dims' M.dag (canonicalIncidence C) i) (M.domain i)) :
    ∃ f : ∀ i, StructuralInput kind dims' M.dag (canonicalIncidence C) i →
        L1Vec (outputDim (kind i)),
      (∀ i, Measurable (f i)) ∧
      (∀ i d, kind i = Sum.inl d → ∀ x,
        f i x = M.continuousMap i (pi i x)) ∧
      (∀ i k, kind i = Sum.inr k → ∀ x,
        x ∈ admissibleStructuralInputs kind dims' M.dag (canonicalIncidence C) i →
        f i x = WithLp.toLp 1 (fun j =>
          (p i (pi i x)).ofLp j / ∑ l, (p i (pi i x)).ofLp l)) ∧
      (∀ i k (hi : kind i = Sum.inr k) x,
        x ∈ admissibleStructuralInputs kind dims' M.dag (canonicalIncidence C) i →
        (fun j : Fin k => (f i x).ofLp (Fin.cast (congrArg outputDim hi).symm j)) ∈
          stdSimplex ℝ (Fin k)) := by
  classical
  have hw (i : Fin n) :
      ∃ w : StructuralInput kind dims M.dag M.incidence i → L1Vec (outputDim (kind i)),
        Measurable w ∧
        (∀ d, kind i = Sum.inl d → ∀ x, w x = M.continuousMap i x) ∧
        (∀ k, kind i = Sum.inr k → ∀ x ∈ M.domain i,
          w x = WithLp.toLp 1 (fun j => (p i x).ofLp j / ∑ l, (p i x).ofLp l)) := by
    by_cases h : ∃ k, kind i = Sum.inr k
    · obtain ⟨k, hi⟩ := h
      obtain ⟨w, hm, he⟩ := exists_measurable_normalized_propensity M p hcat i k hi
      refine ⟨w, hm, ?_, fun _ _ => he⟩
      intro d hd
      cases hd.symm.trans hi
    · refine ⟨M.continuousMap i, by fun_prop, fun _ _ _ => rfl, ?_⟩
      intro k hk
      exact (h ⟨k,hk⟩).elim
  choose w hm hcontinuous hcategorical using hw
  refine ⟨fun i => w i ∘ pi i, ?_, ?_, ?_, ?_⟩
  · intro i
    let : BorelSpace (StructuralInput kind dims' M.dag (canonicalIncidence C) i) := ⟨rfl⟩
    let : BorelSpace (StructuralInput kind dims M.dag M.incidence i) := ⟨rfl⟩
    exact (hm i).comp (pi i).continuous.measurable
  · intro i d hi x
    exact hcontinuous i d hi (pi i x)
  · intro i k hi x hx
    exact hcategorical i k hi (pi i x) (hpi i hx)
  · intro i k hi x hx
    change (fun j : Fin k => (w i (pi i x)).ofLp _) ∈ _
    rw [hcategorical i k hi (pi i x) (hpi i hx)]
    have hp := canonical_normalized_mem_simplex (p i (pi i x)).ofLp
      (hcat.1 i k hi (pi i x) (hpi i hx)).1
      (hcat.1 i k hi (pi i x) (hpi i hx)).2
    refine ⟨fun j => hp.1 _, ?_⟩
    exact (Equiv.sum_comp (finCongr (congrArg outputDim hi).symm)
      (fun j => (p i (pi i x)).ofLp j / ∑ l, (p i (pi i x)).ofLp l)).trans hp.2

end
end Papers.TbsNeuralCausalPi
