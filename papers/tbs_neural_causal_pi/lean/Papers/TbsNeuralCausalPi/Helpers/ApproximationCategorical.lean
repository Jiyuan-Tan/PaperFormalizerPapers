module
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationContinuous
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationSelectorStep
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalCategoricalTransition
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalLatentIndependence
/-! # Categorical updates on augmented approximation histories

Pull back the structural propensity to histories retaining the non-Gumbel
latents. The encoded maximal coupling gives the local categorical bound on
the visited carrying domain, including zero simplex coordinates.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: approximationHistory_erase_current_gumbels
/-- At [an evaluation step no later than the position of node i in the causal order](hyp:hr),
[zeroing that node's intrinsic noise leaves the augmented history unchanged](goal). -/
lemma approximationHistory_erase_current_gumbels (M : EuclideanSCM kind dims)
    (i : Fin n) (t : Intervention kind) (u : Exogenous kind dims)
    (r : ℕ) (hr : r ≤ M.dag.topoOrder i) :
    approximationHistory M t u r = approximationHistory M t
      (restrictLatentFamily ({Sum.inr i} : Finset (Fin b ⊕ Fin n))ᶜ u) r := by
  unfold approximationHistory
  rw [evalSteps_erase_current_gumbels M i t u r hr]
  congr 1
  funext j
  cases j with
  | inl j =>
    change _ = if Sum.inl j.1 ∈ ({Sum.inr i} : Finset (Fin b ⊕ Fin n))ᶜ then _ else 0
    simp
  | inr j => rfl

-- @node: approximationHistory_indep_current_gumbels
/-- If [the model's latent blocks are independent](hyp:hind) and
[node i is categorical with k categories](hyp:hi), then
[the augmented history just before that node is evaluated is independent of its
vector of intrinsic categorical noises](goal). -/
lemma approximationHistory_indep_current_gumbels (M : EuclideanSCM kind dims)
    (hind : LatentBlocksIndependent M) (i : Fin n) (t : Intervention kind)
    (k : ℕ) (hi : kind i = .inr k) :
    ProbabilityTheory.IndepFun (fun u => approximationHistory M t u (M.dag.topoOrder i))
      (fun u (l : Fin k) => (categoricalNoise i u).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l)) M.latentLaw := by
  let S : Finset (Fin b ⊕ Fin n) := {Sum.inr i}
  let X := fun u => approximationHistory M t u (M.dag.topoOrder i)
  let g := fun (u : Exogenous kind dims) (l : Fin k) => (categoricalNoise i u).ofLp
    (Fin.cast (congrArg noiseDim hi).symm l)
  have hX : Measurable X := by fun_prop
  have hg : Measurable g := by fun_prop
  have heX : X ∘ restrictLatentFamily Sᶜ = X := by
    funext u
    exact (approximationHistory_erase_current_gumbels M i t u _ le_rfl).symm
  have heg : g ∘ restrictLatentFamily S = g := by
    funext u l
    change (if Sum.inr i ∈ S then _ else 0) = _
    simp only [S, Finset.mem_singleton_self, if_true]
    rfl
  have h := (restrictLatentFamily_indepFun M hind Sᶜ S disjoint_compl_left).comp hX hg
  simpa only [heX, heg] using h

-- @node: approximationHistory_gumbels_joint_law_of_noise_law
/-- If [the latent blocks are independent](hyp:hind),
[node i is categorical with k categories](hyp:hi), and
[its intrinsic noise vector has the standard k-dimensional Gumbel input law](hyp:hnoise),
then [the joint law of its pre-update augmented history and its noise vector is
the product of the history law and that Gumbel law](goal). -/
lemma approximationHistory_gumbels_joint_law_of_noise_law (M : EuclideanSCM kind dims)
    (hind : LatentBlocksIndependent M) (i : Fin n) (t : Intervention kind)
    (k : ℕ) (hi : kind i = .inr k)
    (hnoise : M.latentLaw.map (fun u (l : Fin k) => (categoricalNoise i u).ofLp
      (Fin.cast (congrArg noiseDim hi).symm l)) = gumbelInputs k) :
    M.latentLaw.map (fun u => (approximationHistory M t u (M.dag.topoOrder i),
      fun l : Fin k => (categoricalNoise i u).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l))) =
      (M.latentLaw.map (fun u => approximationHistory M t u (M.dag.topoOrder i))).prod
        (gumbelInputs k) := by
  let := M.probability
  rw [(approximationHistory_indep_current_gumbels M hind i t k hi).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop)]
  exact congrArg ((M.latentLaw.map (fun u => approximationHistory M t u (M.dag.topoOrder i))).prod)
    hnoise

-- @node: approximationHistory_gumbels_joint_law
/-- If [the latent blocks are independent](hyp:hind),
[categorical mechanisms use the Gumbel argmax representation with the given mechanism weights](hyp:hcat),
and [node i is categorical with k categories](hyp:hi), then
[the joint law of its pre-update augmented history and its intrinsic noise vector
is the product of the history law and the standard k-dimensional Gumbel input law](goal). -/
lemma approximationHistory_gumbels_joint_law (M : EuclideanSCM kind dims)
    (p : MechanismWeights M) (hind : LatentBlocksIndependent M)
    (hcat : CategoricalGumbelArgmax M p) (i : Fin n) (t : Intervention kind)
    (k : ℕ) (hi : kind i = .inr k) :
    M.latentLaw.map (fun u => (approximationHistory M t u (M.dag.topoOrder i),
      fun l : Fin k => (categoricalNoise i u).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l))) =
      (M.latentLaw.map (fun u => approximationHistory M t u (M.dag.topoOrder i))).prod
        (gumbelInputs k) := by
  exact approximationHistory_gumbels_joint_law_of_noise_law M hind i t k hi
    (hcat.2.2.2 i k hi)

-- @node: approximationHistoryPropensity
/-- For [a canonical structural causal model](hyp:M) on [n nodes](hyp:n) of
[the specified node types](hyp:kind), with [b shared latent blocks](hyp:b) of
[the specified dimensions](hyp:dims), [a causal directed acyclic graph](hyp:dag),
[a shared-latent graph](hyp:G), and [latent-to-node incidence sets](hyp:C),
the [history-based propensity vector](goal) at [node i](hyp:i), with
[k categories](hyp:k) and [categorical type](hyp:hi), evaluates the node's structural
mechanism at the parent values and retained latent inputs extracted from
[the augmented history](hyp:x), expressing the result as a k-dimensional vector. -/
def approximationHistoryPropensity (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (k : ℕ) (hi : kind i = .inr k)
    (x : ApproximationHistorySpace kind dims) : L1Vec k :=
  WithLp.toLp 1 (fun j => (M.f i (approximationHistoryInput i x)).ofLp
    (Fin.cast (congrArg outputDim hi).symm j))

-- @node: approximationHistoryPropensity_measurable
/-- For [a node with k categorical outcomes](hyp:hi),
[the propensity vector is a measurable function of the augmented history](goal). -/
@[fun_prop] lemma approximationHistoryPropensity_measurable
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ)
    (hi : kind i = .inr k) : Measurable (approximationHistoryPropensity M i k hi) := by
  have hf := M.structuralMeasurable i
  fun_prop [approximationHistoryPropensity]

-- @node: approximationHistoryPropensity_simplex
/-- If [node i has k categorical outcomes](hyp:hi) and
[the augmented history lies in the admissible domain just before that node's update](hyp:hx),
then [its propensity vector has nonnegative entries summing to one](goal). -/
lemma approximationHistoryPropensity_simplex (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (k : ℕ) (hi : kind i = .inr k)
    (x : ApproximationHistorySpace kind dims)
    (hx : x ∈ approximationHistoryDomain (dag := dag) (dag.topoOrder i)) :
    (approximationHistoryPropensity M i k hi x).ofLp ∈ probabilitySimplex k := by
  exact M.simplex i k hi _ (approximationHistoryInput_mem_domain M i x hx).1

-- @node: approximationHistoryPropensity_edist
/-- For [a node with k categorical outcomes](hyp:hi),
[the extended L1 distance between the two models' history-based propensity vectors
equals the extended L1 distance between their structural mechanism outputs at
the corresponding extracted inputs](goal). -/
lemma approximationHistoryPropensity_edist (M N : CanonicalSCM kind dims dag G C)
    (i : Fin n) (k : ℕ) (hi : kind i = .inr k)
    (x y : ApproximationHistorySpace kind dims) :
    edist (approximationHistoryPropensity M i k hi x)
      (approximationHistoryPropensity N i k hi y) =
    edist (M.f i (approximationHistoryInput i x))
      (N.f i (approximationHistoryInput i y)) := by
  simp only [approximationHistoryPropensity, PiLp.edist_eq_of_L1]
  exact Function.Bijective.sum_comp
    (show Function.Bijective (Fin.cast (congrArg outputDim hi).symm) from
      ⟨Fin.cast_injective _, fun j => ⟨Fin.cast (congrArg outputDim hi) j, by simp⟩⟩)
    (fun j => edist ((M.f i (approximationHistoryInput i x)).ofLp j)
      ((N.f i (approximationHistoryInput i y)).ofLp j))

-- @node: approximationHistoryPropensity_lipschitzOn
/-- For [a node with k categorical outcomes](hyp:hi) and
[a nonnegative constant L](hyp:L), if [its structural mechanism is L-Lipschitz
on its input domain](hyp:hLip), then [the history-based propensity vector is
L-Lipschitz on the admissible pre-update history domain](goal). -/
lemma approximationHistoryPropensity_lipschitzOn
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ) (hi : kind i = .inr k)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (M.f i) (M.domain i)) :
    LipschitzOnWith L (approximationHistoryPropensity M i k hi)
      (approximationHistoryDomain (dag := dag) (dag.topoOrder i)) := by
  have hin : LipschitzWith 1 (approximationHistoryInput (kind := kind) (dims := dims)
      (dag := dag) (C := C) i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa using approximationHistoryInput_dist_le (dag := dag) (C := C) i x y
  intro x hx y hy
  rw [approximationHistoryPropensity_edist]
  refine (hLip (approximationHistoryInput_mem_domain M i x hx)
    (approximationHistoryInput_mem_domain M i y hy)).trans ?_
  have h := hin x y
  rw [ENNReal.coe_one, one_mul] at h
  exact mul_le_mul' le_rfl h

-- @node: approximationHistoryPropensity_supDistOn_le
/-- For [a node with k categorical outcomes](hyp:hi),
[the uniform distance between two models' propensity vectors on the admissible
pre-update history domain is bounded by the uniform distance between their
structural mechanisms on the node's input domain](goal). -/
lemma approximationHistoryPropensity_supDistOn_le
    (M N : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ) (hi : kind i = .inr k) :
    supDistOn (approximationHistoryDomain (dag := dag) (dag.topoOrder i))
      (approximationHistoryPropensity M i k hi) (approximationHistoryPropensity N i k hi) ≤
      supDistOn (M.domain i) (M.f i) (N.f i) := by
  apply iSup_le
  intro x
  apply le_iSup_of_le (⟨approximationHistoryInput i x.val,
    approximationHistoryInput_mem_domain M i x.val x.property⟩ : M.domain i)
  apply ENNReal.ofReal_le_ofReal
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro j
  exact norm_le_pi_norm
    ((M.f i (approximationHistoryInput i x.val) -
      N.f i (approximationHistoryInput i x.val)).ofLp)
    (Fin.cast (congrArg outputDim hi).symm j)

-- @node: approximationCategoricalValue
/-- For [node i](hyp:i) among [n nodes](hyp:n) with [the specified node types](hyp:kind),
and [a category index j](hyp:j) among [k categories](hyp:k), the
[encoded categorical value](goal) is the vector whose every coordinate equals
the one-based label of category j, with the dimension of the node's value space. -/
def approximationCategoricalValue (i : Fin n) (k : ℕ) (j : Fin k) :
    L1Vec (valueDim (kind i)) := WithLp.toLp 1 (fun _ => (j.val + 1 : ℝ))

-- @node: approximationCategoricalValue_dist_le
/-- If [node i has k categorical outcomes](hyp:hi), then
[the distance between the encodings of two categories is at most zero when they
agree and at most k minus one when they differ](goal). -/
lemma approximationCategoricalValue_dist_le (i : Fin n) (k : ℕ)
    (hi : kind i = .inr k) (a c : Fin k) :
    dist (approximationCategoricalValue (kind := kind) i k a)
      (approximationCategoricalValue (kind := kind) i k c) ≤
      if a = c then 0 else ((k-1 : ℕ) : ℝ) := by
  by_cases hac : a = c
  · simp [hac]
  · rw [if_neg hac, PiLp.dist_eq_of_L1]
    change (∑ _j : Fin (valueDim (kind i)), dist (a.val + 1 : ℝ) (c.val + 1 : ℝ)) ≤ _
    rw [Finset.sum_const]
    have hc : (Finset.univ : Finset (Fin (valueDim (kind i)))).card = 1 := by
      rw [Finset.card_univ, Fintype.card_fin, hi]
      rfl
    rw [hc, one_smul]
    exact categorical_label_diameter_le a c

-- @node: approximationCategoricalUpdate
/-- For [node i](hyp:i) among [n nodes](hyp:n) with [the specified node types](hyp:kind),
and [b retained latent blocks](hyp:b) of [the specified dimensions](hyp:dims),
the [categorical history update](goal) replaces that node's value in
[an augmented history](hyp:x) by the one-based encoding of [category j](hyp:j)
among [k categories](hyp:k), retaining all other coordinates. -/
def approximationCategoricalUpdate (i : Fin n) (k : ℕ)
    (x : ApproximationHistorySpace kind dims) (j : Fin k) :=
  approximationHistorySetNode i (approximationCategoricalValue i k j) x

-- @node: approximationCategoricalUpdate_measurable
/-- [Updating a fixed node to a fixed category is a measurable function of
the augmented history](goal). -/
@[fun_prop] lemma approximationCategoricalUpdate_measurable
    (i : Fin n) (k : ℕ) (j : Fin k) :
    Measurable (fun x : ApproximationHistorySpace kind dims =>
      approximationCategoricalUpdate i k x j) := by
  fun_prop [approximationCategoricalUpdate]

-- @node: approximationCategoricalUpdate_dist_le
/-- If [node i has k categorical outcomes](hyp:hi), then
[the distance between two updated histories is at most their original distance
plus zero for matching categories or k minus one for different categories](goal). -/
lemma approximationCategoricalUpdate_dist_le (i : Fin n) (k : ℕ) (hi : kind i = .inr k)
    (x y : ApproximationHistorySpace kind dims) (a c : Fin k) :
    dist (approximationCategoricalUpdate i k x a) (approximationCategoricalUpdate i k y c) ≤
      dist x y + if a = c then 0 else ((k-1 : ℕ) : ℝ) := by
  have h := approximationHistorySetNode_edist_le i
    (approximationCategoricalValue i k a) (approximationCategoricalValue i k c) x y
  rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h.trans (add_le_add le_rfl (approximationCategoricalValue_dist_le i k hi a c))

-- @node: nodeValue_categorical_coordinate
lemma nodeValue_categorical_coordinate (M : EuclideanSCM kind dims)
    (i : Fin n) (k : ℕ) (hi : kind i = .inr k)
    (v : Joint kind) (u : Exogenous kind dims) (j : Fin (valueDim (kind i))) :
    (nodeValue M i v u).ofLp j =
      ((M.categoricalLabel i k hi (structuralInput M i v u)
        (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
          (Fin.cast (congrArg noiseDim hi).symm l)))).val + 1 : ℝ) := by
  rw [categoricalLabel_actual_noise]
  have h (κ : NodeKind) (hκ : κ = .inr k) (y : ObservedValue κ)
      (l : Fin (valueDim κ)) :
      (observedValueEmbedding κ y).ofLp l =
        ((cast (congrArg ObservedValue hκ) y).val + 1 : ℝ) := by
    subst κ
    simp [observedValueEmbedding, Nat.cast_add, Nat.cast_one]
  rw [show nodeValue M i v u = _ from (observedValueEmbedding_eq _ _).symm]
  exact h (kind i) hi _ j

-- @node: approximationHistory_categorical_step_eq
/-- If [node i has k categorical outcomes](hyp:hi) and
[the intervention leaves that node untreated](hyp:ht), then
[the next augmented history is obtained by replacing its value with the category
chosen by the canonical selector from its current propensity vector and actual
intrinsic noise](goal). -/
lemma approximationHistory_categorical_step_eq (M : CanonicalSCM kind dims dag G C)
    (t : Intervention kind) (i : Fin n) (k : ℕ) (hi : kind i = .inr k)
    (ht : t i = none) (u : Exogenous kind dims) :
    approximationHistory M.toEuclideanSCM t u (dag.topoOrder i + 1) =
      approximationCategoricalUpdate i k
        (approximationHistory M.toEuclideanSCM t u (dag.topoOrder i))
        (canonicalSelector (.inr k) (fun m hm => M.positive_categories i m (hi.trans hm))
          (approximationHistoryPropensity M i k hi
            (approximationHistory M.toEuclideanSCM t u (dag.topoOrder i)))
          (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
            (Fin.cast (congrArg noiseDim hi).symm l)))) := by
  apply WithLp.ofLp_injective
  funext j
  cases j with
  | inl j => rfl
  | inr j =>
    rcases j with ⟨j,l⟩
    by_cases hj : j = i
    · subst j
      simp only [approximationHistory, approximationCategoricalUpdate,
        approximationHistorySetNode, approximationCategoricalValue, WithLp.ofLp_toLp,
        Sum.elim_inr, dite_true, Fin.cast_refl, id_eq, evalSteps,
        show M.toEuclideanSCM.dag = dag from rfl, if_true, ht, Option.getD_none]
      rw [nodeValue_categorical_coordinate M.toEuclideanSCM i k hi]
      erw [canonicalMechanism_categoricalLabel_eq M i k hi]
      erw [← approximationHistoryInput_eval M i t u (dag.topoOrder i)]
      rfl
    · have horder : dag.topoOrder j ≠ dag.topoOrder i :=
        fun h => hj (dag.topoOrder_injective h)
      simp only [approximationHistory, approximationCategoricalUpdate,
        approximationHistorySetNode, WithLp.ofLp_toLp, Sum.elim_inr, hj, dite_false,
        evalSteps, show M.toEuclideanSCM.dag = dag from rfl, horder, if_false]

-- @node: approximationHistory_categorical_successor_law_of_noise_law
/-- If [the latent blocks are independent](hyp:hind),
[node i has k categorical outcomes](hyp:hi), [the intervention leaves it untreated](hyp:ht),
and [its intrinsic noise has the standard k-dimensional Gumbel input law](hyp:hnoise),
then [the next augmented-history law is obtained by drawing the current history
and fresh Gumbel inputs independently, selecting a category from the history's
propensity vector, and updating that node](goal). -/
lemma approximationHistory_categorical_successor_law_of_noise_law
    (M : CanonicalSCM kind dims dag G C)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (t : Intervention kind) (i : Fin n) (k : ℕ) (hi : kind i = .inr k)
    (ht : t i = none)
    (hnoise : M.latentLaw.map (fun u (l : Fin k) => (categoricalNoise i u).ofLp
      (Fin.cast (congrArg noiseDim hi).symm l)) = gumbelInputs k) :
    M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t u (dag.topoOrder i + 1)) =
      ((M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t u
        (dag.topoOrder i))).prod (gumbelInputs k)).map (fun z =>
          approximationCategoricalUpdate i k z.1
            (canonicalSelector (.inr k) (fun m hm => M.positive_categories i m (hi.trans hm))
              (approximationHistoryPropensity M i k hi z.1) (WithLp.toLp 1 z.2))) := by
  let F := fun z : ApproximationHistorySpace kind dims × (Fin k → ℝ) =>
    approximationCategoricalUpdate i k z.1
      (canonicalSelector (.inr k) (fun m hm => M.positive_categories i m (hi.trans hm))
        (approximationHistoryPropensity M i k hi z.1) (WithLp.toLp 1 z.2))
  have hp := approximationHistoryPropensity_measurable M i k hi
  have hs : Measurable (fun z : ApproximationHistorySpace kind dims × (Fin k → ℝ) =>
      canonicalSelector (.inr k) (fun m hm => M.positive_categories i m (hi.trans hm))
        (approximationHistoryPropensity M i k hi z.1) (WithLp.toLp 1 z.2)) := by
    have hg : Measurable (fun z : ApproximationHistorySpace kind dims × (Fin k → ℝ) =>
        WithLp.toLp 1 z.2) := by fun_prop
    exact (canonicalSelector_measurable (.inr k)
      (fun m hm => M.positive_categories i m (hi.trans hm))).comp
        ((hp.comp measurable_fst).prodMk hg)
  have hF : Measurable F := by
    have hv : Measurable (fun z : ApproximationHistorySpace kind dims × Fin k =>
        approximationCategoricalUpdate i k z.1 z.2) :=
      measurable_from_prod_countable_left (fun j => approximationCategoricalUpdate_measurable i k j)
    exact hv.comp (measurable_fst.prodMk hs)
  erw [← approximationHistory_gumbels_joint_law_of_noise_law M.toEuclideanSCM hind i t k hi hnoise,
    Measure.map_map hF (by fun_prop)]
  congr 1
  funext u
  exact approximationHistory_categorical_step_eq M t i k hi ht u

-- @node: approximationHistory_categorical_successor_law
/-- If [the latent blocks are independent](hyp:hind),
[the categorical mechanisms satisfy the Gumbel argmax representation](hyp:hcat),
[node i has k categorical outcomes](hyp:hi), and [the intervention leaves it untreated](hyp:ht),
then [the next augmented-history law is obtained by independently drawing a current
history and standard Gumbel inputs and applying the canonical categorical update
with that history's propensity vector](goal). -/
lemma approximationHistory_categorical_successor_law
    (M : CanonicalSCM kind dims dag G C)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (hcat : CategoricalGumbelArgmax M.toEuclideanSCM M.f)
    (t : Intervention kind) (i : Fin n) (k : ℕ) (hi : kind i = .inr k)
    (ht : t i = none) :
    M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t u (dag.topoOrder i + 1)) =
      ((M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t u
        (dag.topoOrder i))).prod (gumbelInputs k)).map (fun z =>
          approximationCategoricalUpdate i k z.1
            (canonicalSelector (.inr k) (fun m hm => M.positive_categories i m (hi.trans hm))
              (approximationHistoryPropensity M i k hi z.1) (WithLp.toLp 1 z.2))) := by
  exact approximationHistory_categorical_successor_law_of_noise_law M hind t i k hi ht
    (hcat.2.2.2 i k hi)

-- @node: approximationHistory_categorical_product_transport_le
/-- For two probability distributions on augmented histories and
[a node with k categorical outcomes](hyp:hi), suppose
[the first history distribution is concentrated on the admissible pre-update domain](hyp:hmu)
and [so is the second](hyp:hnu). Given [a nonnegative constant L](hyp:L) such that
[the first model's structural mechanism is L-Lipschitz on its input domain](hyp:hLip),
[the Wasserstein-1 distance between the two history distributions after their
respective model updates with independent fresh Gumbel inputs is bounded by
the original Wasserstein-1 distance multiplied by the factor 1 + (k − 1)L/2,
plus k(k − 1)/2 times the uniform distance between the structural mechanisms
on the node's input domain](goal). -/
lemma approximationHistory_categorical_product_transport_le
    (M N : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ) (hi : kind i = .inr k)
    (mu nu : Measure (ApproximationHistorySpace kind dims))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : ∀ᵐ x ∂mu, x ∈ approximationHistoryDomain (dag := dag) (dag.topoOrder i))
    (hnu : ∀ᵐ x ∂nu, x ∈ approximationHistoryDomain (dag := dag) (dag.topoOrder i))
    (L : ℝ≥0) (hLip : LipschitzOnWith L (M.f i) (M.domain i)) :
    let hk := fun m hm => M.positive_categories i m (hi.trans hm)
    wasserstein1
      ((mu.prod (gumbelInputs k)).map (fun z => approximationCategoricalUpdate i k z.1
        (canonicalSelector (.inr k) hk (approximationHistoryPropensity M i k hi z.1)
          (WithLp.toLp 1 z.2))))
      ((nu.prod (gumbelInputs k)).map (fun z => approximationCategoricalUpdate i k z.1
        (canonicalSelector (.inr k) hk (approximationHistoryPropensity N i k hi z.1)
          (WithLp.toLp 1 z.2)))) ≤
      ((1 + (k-1 : ℕ) * L / 2 : ℝ≥0) : ℝ≥0∞) * wasserstein1 mu nu +
        ((k * (k-1 : ℕ) / 2 : ℝ≥0) : ℝ≥0∞) *
          supDistOn (M.domain i) (M.f i) (N.f i) := by
  dsimp only
  have h := approximation_selector_history_step
    (fun m hm => M.positive_categories i m (hi.trans hm)) mu nu
    (approximationHistoryDomain (dag := dag) (dag.topoOrder i))
    (approximationHistoryDomain_measurableSet _) hmu hnu
    (approximationHistoryPropensity M i k hi) (approximationHistoryPropensity N i k hi)
    (by fun_prop) (by fun_prop)
    (approximationHistoryPropensity_simplex M i k hi)
    (approximationHistoryPropensity_simplex N i k hi)
    (approximationCategoricalUpdate i k) (by fun_prop) L (k-1 : ℕ)
    (approximationHistoryPropensity_lipschitzOn M i k hi L hLip)
    (fun x _ y _ a c => approximationCategoricalUpdate_dist_le i k hi x y a c)
  exact h.trans (add_le_add le_rfl
    (mul_le_mul' le_rfl (approximationHistoryPropensity_supDistOn_le M N i k hi)))

-- @node: approximationHistory_categorical_step_transport_le
/-- For [a node with k categorical outcomes](hyp:hi) that
[the intervention leaves untreated](hyp:ht), let [L be nonnegative](hyp:L) and
assume [the first canonical model's structural mechanism is L-Lipschitz on its input domain](hyp:hLip).
[The Wasserstein-1 distance between the models' next augmented-history laws is
bounded by their current history-law distance multiplied by the factor
1 + (k − 1)L/2, plus k(k − 1)/2 times the uniform distance between their
structural mechanisms on the node's input domain](goal). -/
lemma approximationHistory_categorical_step_transport_le
    (M N : CanonicalSCM kind dims dag G C) (t : LawIntervention kind)
    (i : Fin n) (k : ℕ) (hi : kind i = .inr k) (ht : t.val i = none)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (M.f i) (M.domain i)) :
    wasserstein1
      (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t.val u
        (dag.topoOrder i + 1)))
      (N.latentLaw.map (fun u => approximationHistory N.toEuclideanSCM t.val u
        (dag.topoOrder i + 1))) ≤
      ((1 + (k-1 : ℕ) * L / 2 : ℝ≥0) : ℝ≥0∞) * wasserstein1
        (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t.val u
          (dag.topoOrder i)))
        (N.latentLaw.map (fun u => approximationHistory N.toEuclideanSCM t.val u
          (dag.topoOrder i))) +
      ((k * (k-1 : ℕ) / 2 : ℝ≥0) : ℝ≥0∞) *
        supDistOn (M.domain i) (M.f i) (N.f i) := by
  let := M.latentLaw_probability
  let := N.latentLaw_probability
  let : IsProbabilityMeasure (M.latentLaw.map (fun u =>
      approximationHistory M.toEuclideanSCM t.val u (dag.topoOrder i))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure (N.latentLaw.map (fun u =>
      approximationHistory N.toEuclideanSCM t.val u (dag.topoOrder i))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hcarry (Q : CanonicalSCM kind dims dag G C) :
      ∀ᵐ x ∂Q.latentLaw.map (fun u => approximationHistory Q.toEuclideanSCM t.val u
        (dag.topoOrder i)), x ∈ approximationHistoryDomain (dag := dag) (dag.topoOrder i) := by
    apply (ae_map_iff (approximationHistory_measurable Q.toEuclideanSCM t.val _).aemeasurable
      (approximationHistoryDomain_measurableSet _)).2
    exact Filter.Eventually.of_forall fun u => approximationHistory_mem_domain Q t u _
  rw [approximationHistory_categorical_successor_law_of_noise_law M
      (canonical_latent_blocks_independent M) t.val i k hi ht
      (canonical_categorical_noise_law M i k hi),
    approximationHistory_categorical_successor_law_of_noise_law N
      (canonical_latent_blocks_independent N) t.val i k hi ht
      (canonical_categorical_noise_law N i k hi)]
  exact approximationHistory_categorical_product_transport_le M N i k hi _ _
    (hcarry M) (hcarry N) L hLip

end
end Papers.TbsNeuralCausalPi
