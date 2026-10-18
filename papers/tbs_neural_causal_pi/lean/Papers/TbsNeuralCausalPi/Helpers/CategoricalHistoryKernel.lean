module
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalCategoricalTransition
public import Papers.TbsNeuralCausalPi.Helpers.EvaluationKernels
/-! # Identification of canonical categorical history transitions

On the carrying domain, the actual private-noise transition is the finite
encoded categorical law with its integrated propensity. No conditional-law
version or strict positivity premise is introduced.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)}

/-- [The canonical node history transition equals the distribution of the history update under the full latent law](goal). -/
-- @node: canonicalNodeHistoryKernel_eq_map_update
lemma canonicalNodeHistoryKernel_eq_map_update
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (t : Intervention kind)
    (v : Joint kind) :
    canonicalNodeHistoryKernel M i t v =
      M.latentLaw.map (fun u => nodeHistoryUpdate M.toEuclideanSCM i t (v,u)) := by
  have hupdate : Measurable (fun u => nodeHistoryUpdate M.toEuclideanSCM i t (v,u)) := by
    fun_prop
  change (M.latentLaw.map (restrictLatentFamily (nodeLatentIndices (C := C) i))).map _ = _
  rw [Measure.map_map hupdate (restrictLatentFamily_measurable _)]
  congr 1
  funext u
  apply WithLp.ofLp_injective
  funext ⟨j,l⟩
  dsimp [nodeHistoryUpdate]
  split_ifs with hj
  · rw [← nodeValue_restrict_node_noise M i v u]
  · rfl

/-- In a system of [n nodes](hyp:n) with [the given node types](hyp:kind), for [a node i](hyp:i), [a joint history v](hyp:v), and [a label among k categories](hyp:label), the [replacement history](goal) assigns the label's index plus one to every coordinate of node i and keeps the other nodes unchanged. -/
-- @node: categoricalHistoryReplacement
def categoricalHistoryReplacement (i : Fin n) (v : Joint kind) {k : ℕ}
    (label : Fin k) : Joint kind :=
  WithLp.toLp 1 (fun ⟨j,l⟩ => if j = i then (label.val + 1 : ℝ) else v.ofLp ⟨j,l⟩)

-- @node: categoricalHistoryReplacement_measurable
/-- [Replacing a fixed node by a fixed categorical label is a measurable function of the joint history](goal). -/
@[fun_prop] lemma categoricalHistoryReplacement_measurable (i : Fin n) {k : ℕ}
    (label : Fin k) : Measurable (fun v : Joint kind => categoricalHistoryReplacement i v label) := by
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  rintro ⟨j,l⟩
  dsimp [categoricalHistoryReplacement]
  split_ifs <;> fun_prop

/-- If [node i has k categories](hyp:hi), [every coordinate of its numerical value equals the selected categorical label's index plus one](goal), using the structural inputs and categorical noise of the given history and exogenous realization. -/
lemma nodeValue_categorical_coordinate (M : EuclideanSCM kind dims) (i : Fin n)
    (k : ℕ) (hi : kind i = Sum.inr k) (v : Joint kind) (u : Exogenous kind dims)
    (j : Fin (valueDim (kind i))) :
    (nodeValue M i v u).ofLp j =
      ((M.categoricalLabel i k hi (structuralInput M i v u)
        (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
          (Fin.cast (congrArg noiseDim hi).symm l)))).val + 1 : ℝ) := by
  have he (a : NodeKind) (h : a = Sum.inr k) (y : ObservedValue a)
      (l : Fin (valueDim a)) :
      (observedValueEmbedding a y).ofLp l =
        ((cast (congrArg ObservedValue h) y).val + 1 : ℝ) := by
    subst a
    simp [observedValueEmbedding]
  have hn : nodeValue M i v u = observedValueEmbedding (kind i)
      (M.f i (structuralInput M i v u) (categoricalNoise i u)) :=
    (observedValueEmbedding_eq (kind i) _).symm
  rw [hn, he (kind i) hi]
  unfold EuclideanSCM.categoricalLabel
  congr 3

/-- If [node i has k categories](hyp:hi), [the intervention leaves it untreated](hyp:hti), [its topological rank is r](hyp:hr), and [the history is in the visited domain at rank r](hyp:hv), [its canonical history transition is the finite mixture of label replacement histories, weighted by the categorical propensities integrated over the independent latent blocks](goal). -/
-- @node: canonicalNodeHistoryKernel_categorical_law
lemma canonicalNodeHistoryKernel_categorical_law
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k) (t : Intervention kind) (hti : t i = none)
    (r : ℕ) (hr : dag.topoOrder i = r) (v : Joint kind)
    (hv : v ∈ visitedHistoryDomain (dag := dag) r) :
    canonicalNodeHistoryKernel M i t v =
      ∑ j, ENNReal.ofReal (∫ z,
        (canonicalCategoricalPropensity M i k hi v z).ofLp j
          ∂(Measure.pi (fun a => (M.blockLaw a : Measure (L1Vec (dims a)))))) •
            Measure.dirac (categoricalHistoryReplacement i v j) := by
  let label := fun u => M.toEuclideanSCM.categoricalLabel i k hi
    (structuralInput M.toEuclideanSCM i v u)
    (WithLp.toLp 1 (fun j => (categoricalNoise i u).ofLp
      (Fin.cast (congrArg noiseDim hi).symm j)))
  have hlabel : Measurable label := by
    have he (u) := canonicalMechanism_categoricalLabel_eq M i k hi
      (structuralInput M.toEuclideanSCM i v u)
      (WithLp.toLp 1 (fun j => (categoricalNoise i u).ofLp
        (Fin.cast (congrArg noiseDim hi).symm j)))
    simp_rw [show label = _ from funext he]
    apply firstArgmax_getD_measurable
    intro j
    have hx : Measurable (fun u : Exogenous kind dims =>
        structuralInput M.toEuclideanSCM i v u) :=
      (structuralInput_measurable M.toEuclideanSCM i).comp
        (measurable_const.prodMk measurable_id)
    have hw := (M.structuralMeasurable i).comp hx
    fun_prop
  have henc : Measurable (categoricalHistoryReplacement (kind := kind) i v (k := k)) :=
    measurable_of_countable _
  have hupdate (u : Exogenous kind dims) :
      nodeHistoryUpdate M.toEuclideanSCM i t (v,u) =
        categoricalHistoryReplacement i v (label u) := by
    apply WithLp.ofLp_injective
    funext ⟨j,l⟩
    dsimp [nodeHistoryUpdate, categoricalHistoryReplacement]
    split_ifs with hj
    · simp only [hti, Option.getD_none]
      exact nodeValue_categorical_coordinate M.toEuclideanSCM i k hi v u _
    · rfl
  calc
    _ = M.latentLaw.map (fun u => categoricalHistoryReplacement i v (label u)) := by
      rw [canonicalNodeHistoryKernel_eq_map_update]
      congr 1
      funext u
      exact hupdate u
    _ = (M.latentLaw.map label).map (categoricalHistoryReplacement i v) :=
      (Measure.map_map henc hlabel).symm
    _ = (∑ j, ENNReal.ofReal (∫ z,
        (canonicalCategoricalPropensity M i k hi v z).ofLp j
          ∂(Measure.pi (fun a => (M.blockLaw a : Measure (L1Vec (dims a)))))) •
            Measure.dirac j).map (categoricalHistoryReplacement i v) := by
      congr 1
      exact canonical_categorical_label_law M i k hi v
        (fun u => structuralInput_mem_domain_of_visitedHistory M.toEuclideanSCM i r hr v hv u)
    _ = _ := by
      rw [← Measure.sum_fintype, Measure.map_sum henc.aemeasurable, Measure.sum_fintype]
      simp_rw [Measure.map_smul, Measure.map_dirac' henc]

end
end Papers.TbsNeuralCausalPi
