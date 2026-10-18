module
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationSchedule
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationTransport
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalEvaluation
public import Papers.TbsNeuralCausalPi.Helpers.InterventionalMoments
/-! # Continuous updates of the actual augmented histories -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: ApproximationHistorySpace
/-- For [node types](hyp:kind) on [n observed nodes](hyp:n) and [latent block
dimensions](hyp:dims) for [b blocks](hyp:b), the [augmented history space](goal)
stores all non-Gumbel latent coordinates and observed-node coordinates as a real
vector with the sum-of-absolute-values norm. -/
abbrev ApproximationHistorySpace (kind : Fin n → NodeKind) (dims : Fin b → ℕ) :=
  WithLp 1 (((Σ j, Fin (dims j)) ⊕ (Σ i, Fin (valueDim (kind i)))) → ℝ)

-- @node: approximationHistoryInput
/-- For [node i](hyp:i) and [an augmented history x](hyp:x), the [structural input
extracted from that history](goal) consists of [the observed coordinates of i's
parents](step:1) and [the latent coordinates of blocks incident to i](step:2).
The coordinates use [the node types](hyp:kind) on [n nodes](hyp:n), [block
dimensions](hyp:dims) for [b blocks](hyp:b), [the causal graph](hyp:dag), and
[the block membership sets](hyp:C). -/
def approximationHistoryInput (i : Fin n) (x : ApproximationHistorySpace kind dims) :
    StructuralInput kind dims dag (canonicalIncidence C) i :=
  WithLp.toLp 1 (fun c => match c with
    | .inl ⟨p,j⟩ => x.ofLp (.inr ⟨p.val,j⟩)
    | .inr ⟨a,j⟩ => x.ofLp (.inl ⟨a.val,j⟩))

-- @node: approximationHistoryInput_measurable
/-- For [node i](hyp:i), [extracting its structural input from an augmented
history is measurable](goal). -/
@[fun_prop] lemma approximationHistoryInput_measurable (i : Fin n) :
    Measurable (approximationHistoryInput (kind := kind) (dims := dims)
      (dag := dag) (C := C) i) := by
  first | fun_prop | skip
  unfold approximationHistoryInput
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  rintro (⟨p,j⟩ | ⟨a,j⟩) <;> fun_prop

-- @node: approximationHistoryInput_eval
/-- For [a canonical causal model](hyp:M), [node i](hyp:i), [an intervention](hyp:t),
[an exogenous realization](hyp:u), and [an evaluation stage r](hyp:r),
[extracting i's input from the augmented history gives exactly its structural
input from the observed evaluation history and the exogenous realization](goal). -/
lemma approximationHistoryInput_eval (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (t : Intervention kind) (u : Exogenous kind dims) (r : ℕ) :
    approximationHistoryInput i (approximationHistory M.toEuclideanSCM t u r) =
      structuralInput M.toEuclideanSCM i (evalSteps M.toEuclideanSCM t u r) u := by
  apply WithLp.ofLp_injective
  funext c
  cases c <;> rfl

-- @node: approximationHistoryInput_dist_le
/-- For [node i](hyp:i) and [two augmented histories](hyp:x,y), [the distance
between their extracted structural inputs is at most the distance between the
histories](goal). -/
lemma approximationHistoryInput_dist_le (i : Fin n)
    (x y : ApproximationHistorySpace kind dims) :
    dist (approximationHistoryInput (dag := dag) (C := C) i x)
      (approximationHistoryInput (dag := dag) (C := C) i y) ≤ dist x y := by
  let e : ((Σ p : {p // p ∈ dag.parents i}, Fin (valueDim (kind p.val))) ⊕
      (Σ a : {a // a ∈ canonicalIncidence C i}, Fin (dims a.val))) →
      ((Σ a, Fin (dims a)) ⊕ (Σ p, Fin (valueDim (kind p)))) :=
    fun c => match c with
      | .inl ⟨p,j⟩ => .inr ⟨p.val,j⟩
      | .inr ⟨a,j⟩ => .inl ⟨a.val,j⟩
  have he : Function.Injective e := by
    rintro (⟨⟨p,hp⟩,j⟩ | ⟨⟨a,ha⟩,j⟩) (⟨⟨q,hq⟩,l⟩ | ⟨⟨a',ha'⟩,l⟩) h
    all_goals simp only [e, Sum.inl.injEq, Sum.inr.injEq] at h
    all_goals cases h <;> rfl
  simp only [PiLp.dist_eq_of_L1]
  have hid (c) : (approximationHistoryInput (dag := dag) (C := C) i x).ofLp c =
      x.ofLp (e c) := by cases c <;> rfl
  have hid' (c) : (approximationHistoryInput (dag := dag) (C := C) i y).ofLp c =
      y.ofLp (e c) := by cases c <;> rfl
  simp only [hid, hid']
  rw [← Finset.sum_image (s := Finset.univ) (g := e)
    (f := fun j => dist (x.ofLp j) (y.ofLp j)) he.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => dist_nonneg)

-- @node: approximationHistoryDomain
/-- At [stage r](hyp:r), the [admissible augmented history domain](goal) consists
of histories whose already visited categorical nodes carry valid labels, with
no restriction on other coordinates. It uses [the causal ordering](hyp:dag),
[the node types](hyp:kind) for [n nodes](hyp:n), and [latent block dimensions](hyp:dims)
for [b blocks](hyp:b). -/
def approximationHistoryDomain (r : ℕ) : Set (ApproximationHistorySpace kind dims) :=
  {x | WithLp.toLp 1 (fun j => x.ofLp (.inr j)) ∈
    visitedHistoryDomain (dag := dag) r}

-- @node: approximationHistoryDomain_measurableSet
/-- At [any evaluation stage r](hyp:r), [the admissible augmented history domain
is a measurable set](goal). -/
lemma approximationHistoryDomain_measurableSet (r : ℕ) :
    MeasurableSet (approximationHistoryDomain (kind := kind) (dims := dims) (dag := dag) r) := by
  exact (visitedHistoryDomain_measurableSet r).preimage (by fun_prop)

-- @node: approximationHistory_mem_domain
/-- For [a canonical causal model](hyp:M), [an admissible intervention](hyp:t),
[any exogenous realization](hyp:u), and [any stage r](hyp:r), [the actual augmented
evaluation history belongs to the admissible history domain at that stage](goal). -/
lemma approximationHistory_mem_domain (M : CanonicalSCM kind dims dag G C)
    (t : LawIntervention kind) (u : Exogenous kind dims) (r : ℕ) :
    approximationHistory M.toEuclideanSCM t.val u r ∈
      approximationHistoryDomain (dag := dag) r := by
  exact evalSteps_mem_visitedHistoryDomain M.toEuclideanSCM t.val t.property u r

-- @node: approximationHistoryInput_mem_domain
/-- For [a canonical causal model](hyp:M), [node i](hyp:i), and [an augmented
history x](hyp:x), if [x is admissible at the stage immediately before i is
evaluated](hyp:hx), then [the structural input extracted for i lies in the
model's structural domain for i](goal). -/
lemma approximationHistoryInput_mem_domain (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (x : ApproximationHistorySpace kind dims)
    (hx : x ∈ approximationHistoryDomain (dag := dag) (dag.topoOrder i)) :
    approximationHistoryInput i x ∈ M.domain i := by
  refine ⟨?_, Set.mem_univ _⟩
  intro p k hk
  exact hx p.val k hk (dag.topoOrder_lt _ _ (dag.mem_parents.mp p.property))

-- @node: approximationHistorySetNode_edist_values_le
/-- For [node i](hyp:i), [two candidate values for i](hyp:v,w), and [one augmented
history](hyp:x), [replacing i by the respective values produces histories whose
extended distance is at most the extended distance between those values](goal). -/
lemma approximationHistorySetNode_edist_values_le (i : Fin n)
    (v w : L1Vec (valueDim (kind i))) (x : ApproximationHistorySpace kind dims) :
    edist (approximationHistorySetNode i v x) (approximationHistorySetNode i w x) ≤
      edist v w := by
  simp only [approximationHistorySetNode, PiLp.edist_eq_of_L1, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, edist_self, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ j : Fin n, if j = i then (∑ l, edist (v.ofLp l) (w.ofLp l)) else 0 := by
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j; simp
      · simp [hj]
    _ = _ := by simp

-- @node: approximationHistorySetNode_edist_le
/-- For [node i](hyp:i), [two replacement values](hyp:v,w), and [two augmented
histories](hyp:x,y), [the extended distance after replacing i in each history is
at most the original history distance plus the replacement-value distance](goal). -/
lemma approximationHistorySetNode_edist_le (i : Fin n)
    (v w : L1Vec (valueDim (kind i))) (x y : ApproximationHistorySpace kind dims) :
    edist (approximationHistorySetNode i v x) (approximationHistorySetNode i w y) ≤
      edist x y + edist v w := by
  exact (edist_triangle _ (approximationHistorySetNode i v y) _).trans
    (add_le_add (approximationHistorySetNode_nonexpansive i v x y)
      (approximationHistorySetNode_edist_values_le i v w y))

-- @node: approximationContinuousValue
/-- For [a canonical causal model](hyp:M), [node i](hyp:i), [dimension d](hyp:d),
and [an augmented history x](hyp:x), assuming [i is a continuous node of dimension
d](hyp:hi), the [continuous value at i](goal) is its structural mechanism evaluated
at the input extracted from x, expressed in observed-value coordinates. The model
uses [n nodes](hyp:n), [b latent blocks](hyp:b), [node types](hyp:kind), [block
dimensions](hyp:dims), [a causal graph](hyp:dag), [an undirected graph](hyp:G), and
[block membership sets](hyp:C). -/
def approximationContinuousValue (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (d : ℕ) (hi : kind i = .inl d) (x : ApproximationHistorySpace kind dims) :
    L1Vec (valueDim (kind i)) :=
  WithLp.toLp 1 (fun j => (M.f i (approximationHistoryInput i x)).ofLp
    (Fin.cast (by simp [hi, valueDim, outputDim]) j))

-- @node: approximationContinuousValue_measurable
/-- For [a canonical causal model](hyp:M), [node i](hyp:i), and [dimension d](hyp:d),
if [i is continuous with dimension d](hyp:hi), then [its continuous value is a
measurable function of the augmented history](goal). -/
@[fun_prop] lemma approximationContinuousValue_measurable
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (d : ℕ) (hi : kind i = .inl d) :
    Measurable (approximationContinuousValue M i d hi) := by
  have hf := M.structuralMeasurable i
  fun_prop [approximationContinuousValue]

-- @node: approximationContinuousValue_edist
/-- For [two canonical causal models](hyp:M,N), [node i](hyp:i), [dimension d](hyp:d),
and [two augmented histories](hyp:x,y), if [i is continuous with dimension d](hyp:hi),
then [the extended distance between the models' continuous values at those histories
equals the distance between their structural outputs at the extracted inputs](goal). -/
lemma approximationContinuousValue_edist (M N : CanonicalSCM kind dims dag G C)
    (i : Fin n) (d : ℕ) (hi : kind i = .inl d) (x y : ApproximationHistorySpace kind dims) :
    edist (approximationContinuousValue M i d hi x) (approximationContinuousValue N i d hi y) =
      edist (M.f i (approximationHistoryInput i x)) (N.f i (approximationHistoryInput i y)) := by
  simp only [approximationContinuousValue, PiLp.edist_eq_of_L1]
  exact Function.Bijective.sum_comp
    (show Function.Bijective (Fin.cast (by simp [hi, valueDim, outputDim] :
      valueDim (kind i) = outputDim (kind i))) from
      ⟨Fin.cast_injective _, fun j => ⟨Fin.cast (by simp [hi, valueDim, outputDim]) j, by simp⟩⟩)
    (fun j => edist ((M.f i (approximationHistoryInput i x)).ofLp j)
      ((N.f i (approximationHistoryInput i y)).ofLp j))

-- @node: approximationHistory_continuous_step_eq
/-- For [a canonical causal model](hyp:M), [an intervention](hyp:t), [node i](hyp:i),
[dimension d](hyp:d), and [an exogenous realization](hyp:u), if [i is continuous
with dimension d](hyp:hi) and [the intervention leaves i untouched](hyp:ht), then
[the augmented history immediately after evaluating i is the preceding history
with i replaced by its continuous structural value](goal). -/
lemma approximationHistory_continuous_step_eq (M : CanonicalSCM kind dims dag G C)
    (t : Intervention kind) (i : Fin n) (d : ℕ) (hi : kind i = .inl d) (ht : t i = none)
    (u : Exogenous kind dims) :
    approximationHistory M.toEuclideanSCM t u (dag.topoOrder i + 1) =
      approximationHistorySetNode i
        (approximationContinuousValue M i d hi
          (approximationHistory M.toEuclideanSCM t u (dag.topoOrder i)))
        (approximationHistory M.toEuclideanSCM t u (dag.topoOrder i)) := by
  apply WithLp.ofLp_injective
  funext j
  cases j with
  | inl j => rfl
  | inr j =>
    rcases j with ⟨j,k⟩
    by_cases hj : j = i
    · subst j
      simp only [approximationHistory, approximationHistorySetNode, WithLp.ofLp_toLp,
        Sum.elim_inr, dite_true, Fin.cast_refl, id_eq, evalSteps,
        show M.toEuclideanSCM.dag = dag from rfl, if_true, ht, Option.getD_none]
      rw [nodeValue_continuous_coordinate M.toEuclideanSCM i d hi]
      have hm := canonical_continuousMap_eq_weights M i d hi
        (structuralInput M.toEuclideanSCM i (evalSteps M.toEuclideanSCM t u (dag.topoOrder i)) u)
      rw [hm]
      change _ = (M.f i (approximationHistoryInput i
        (approximationHistory M.toEuclideanSCM t u (dag.topoOrder i)))).ofLp _
      exact congrArg (fun x => (M.f i x).ofLp
        (Fin.cast (by simp [hi, valueDim, outputDim]) k))
        (approximationHistoryInput_eval M i t u (dag.topoOrder i)).symm
    · have horder : dag.topoOrder j ≠ dag.topoOrder i :=
        fun h => hj (dag.topoOrder_injective h)
      simp only [approximationHistory, approximationHistorySetNode, WithLp.ofLp_toLp,
        Sum.elim_inr, hj, dite_false, evalSteps,
        show M.toEuclideanSCM.dag = dag from rfl, horder, if_false]

-- @node: approximationContinuousUpdate
/-- For [a canonical causal model](hyp:M), [node i](hyp:i), [dimension d](hyp:d),
and [an augmented history x](hyp:x), assuming [i is continuous with dimension
d](hyp:hi), the [continuous history update](goal) replaces i in x by its structural
value computed from x. The model uses [n nodes](hyp:n), [b latent blocks](hyp:b),
[node types](hyp:kind), [block dimensions](hyp:dims), [a causal graph](hyp:dag),
[an undirected graph](hyp:G), and [block membership sets](hyp:C). -/
def approximationContinuousUpdate (M : CanonicalSCM kind dims dag G C)
    (i : Fin n) (d : ℕ) (hi : kind i = .inl d) (x : ApproximationHistorySpace kind dims) :=
  approximationHistorySetNode i (approximationContinuousValue M i d hi x) x

-- @node: approximationContinuousUpdate_measurable
/-- For [a canonical causal model](hyp:M), [node i](hyp:i), and [dimension d](hyp:d),
if [i is continuous with dimension d](hyp:hi), then [updating i's value in an
augmented history is a measurable operation](goal). -/
@[fun_prop] lemma approximationContinuousUpdate_measurable
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (d : ℕ) (hi : kind i = .inl d) :
    Measurable (approximationContinuousUpdate M i d hi) := by
  first | fun_prop | skip
  unfold approximationContinuousUpdate approximationHistorySetNode
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  intro j
  cases j with
  | inl j =>
    dsimp only [Sum.elim_inl]
    fun_prop
  | inr j =>
    dsimp only [Sum.elim_inr]
    have hv := approximationContinuousValue_measurable M i d hi
    split_ifs
    · exact (measurable_pi_apply _).comp (scm_ofLp_measurable.comp hv)
    · fun_prop

-- @node: approximationContinuousUpdate_lipschitzOn
/-- For [a canonical causal model](hyp:M), [node i](hyp:i), and [dimension d](hyp:d),
assume [i is continuous with dimension d](hyp:hi). For [a nonnegative constant
L](hyp:L), if [i's structural mechanism is L-Lipschitz on its structural domain](hyp:hLip),
then [the continuous history update is (1 + L)-Lipschitz on the admissible history
domain immediately before i is evaluated](goal). -/
lemma approximationContinuousUpdate_lipschitzOn
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (d : ℕ) (hi : kind i = .inl d)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (M.f i) (M.domain i)) :
    LipschitzOnWith (1+L) (approximationContinuousUpdate M i d hi)
      (approximationHistoryDomain (dag := dag) (dag.topoOrder i)) := by
  have hin : LipschitzWith 1 (approximationHistoryInput (kind := kind) (dims := dims)
      (dag := dag) (C := C) i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa using approximationHistoryInput_dist_le (dag := dag) (C := C) i x y
  intro x hx y hy
  calc
    _ ≤ edist x y + edist (approximationContinuousValue M i d hi x)
        (approximationContinuousValue M i d hi y) :=
      approximationHistorySetNode_edist_le i _ _ x y
    _ ≤ edist x y + (L : ℝ≥0∞) * edist x y := by
      rw [approximationContinuousValue_edist]
      apply add_le_add le_rfl
      refine (hLip (approximationHistoryInput_mem_domain M i x hx)
        (approximationHistoryInput_mem_domain M i y hy)).trans ?_
      apply mul_le_mul_right _ (L : ℝ≥0∞)
      have hh := hin x y
      rw [ENNReal.coe_one, one_mul] at hh
      exact hh
    _ = _ := by simp only [ENNReal.coe_add, ENNReal.coe_one, add_mul, one_mul]

-- @node: approximationContinuousUpdate_error_le
/-- For [two canonical causal models](hyp:M,N), [node i](hyp:i), [dimension d](hyp:d),
and [an augmented history x](hyp:x), suppose [i is continuous with dimension
d](hyp:hi) and [x is admissible immediately before i is evaluated](hyp:hx). Then
[the extended distance between the two updates of x is at most d times the
uniform coordinatewise discrepancy between their mechanisms on the first model's
structural domain](goal). -/
lemma approximationContinuousUpdate_error_le
    (M N : CanonicalSCM kind dims dag G C) (i : Fin n) (d : ℕ) (hi : kind i = .inl d)
    (x : ApproximationHistorySpace kind dims)
    (hx : x ∈ approximationHistoryDomain (dag := dag) (dag.topoOrder i)) :
    edist (approximationContinuousUpdate M i d hi x) (approximationContinuousUpdate N i d hi x) ≤
      (d : ℝ≥0∞) * supDistOn (M.domain i) (M.f i) (N.f i) := by
  have h := approximationHistorySetNode_edist_values_le i
    (approximationContinuousValue M i d hi x) (approximationContinuousValue N i d hi x) x
  rw [approximationContinuousValue_edist] at h
  exact h.trans (by
    simpa only [hi, outputDim] using approximation_edist_le_dim_supDistOn
      (M.domain i) (M.f i) (N.f i) (approximationHistoryInput_mem_domain M i x hx))

-- @node: approximationHistory_continuous_step_transport_le
/-- For [two canonical causal models](hyp:M,N), [an admissible intervention](hyp:t),
[node i](hyp:i), and [dimension d](hyp:d), suppose [i is continuous with dimension
d](hyp:hi) and [the intervention leaves i untouched](hyp:ht). For [a nonnegative
constant L](hyp:L), if [the first model's mechanism at i is L-Lipschitz on its
structural domain](hyp:hLip), then [the Wasserstein distance between the actual
augmented history laws after evaluating i is at most (1 + L) times their preceding
distance plus d times the uniform coordinatewise mechanism discrepancy on that
domain](goal). -/
lemma approximationHistory_continuous_step_transport_le
    (M N : CanonicalSCM kind dims dag G C) (t : LawIntervention kind)
    (i : Fin n) (d : ℕ) (hi : kind i = .inl d) (ht : t.val i = none)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (M.f i) (M.domain i)) :
    wasserstein1
      (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t.val u
        (dag.topoOrder i + 1)))
      (N.latentLaw.map (fun u => approximationHistory N.toEuclideanSCM t.val u
        (dag.topoOrder i + 1))) ≤
      ((1+L : ℝ≥0) : ℝ≥0∞) * wasserstein1
        (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t.val u (dag.topoOrder i)))
        (N.latentLaw.map (fun u => approximationHistory N.toEuclideanSCM t.val u (dag.topoOrder i))) +
      (d : ℝ≥0∞) * supDistOn (M.domain i) (M.f i) (N.f i) := by
  letI := M.latentLaw_probability
  letI := N.latentLaw_probability
  letI : IsProbabilityMeasure (M.latentLaw.map (fun u =>
      approximationHistory M.toEuclideanSCM t.val u (dag.topoOrder i))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (N.latentLaw.map (fun u =>
      approximationHistory N.toEuclideanSCM t.val u (dag.topoOrder i))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hcarry (Q : CanonicalSCM kind dims dag G C) :
      ∀ᵐ x ∂Q.latentLaw.map (fun u => approximationHistory Q.toEuclideanSCM t.val u
        (dag.topoOrder i)), x ∈ approximationHistoryDomain (dag := dag) (dag.topoOrder i) := by
    apply (ae_map_iff (approximationHistory_measurable Q.toEuclideanSCM t.val _).aemeasurable
      (approximationHistoryDomain_measurableSet _)).2
    exact Filter.Eventually.of_forall fun u => approximationHistory_mem_domain Q t u _
  have h := approximation_wasserstein_map_perturbation_le
    (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t.val u (dag.topoOrder i)))
    (N.latentLaw.map (fun u => approximationHistory N.toEuclideanSCM t.val u (dag.topoOrder i)))
    _ (hcarry M) (hcarry N)
    (approximationContinuousUpdate M i d hi) (approximationContinuousUpdate N i d hi)
    (by fun_prop) (by fun_prop) (1+L)
    (approximationContinuousUpdate_lipschitzOn M i d hi L hLip) _
    (approximationContinuousUpdate_error_le M N i d hi)
  rw [Measure.map_map (by fun_prop) (approximationHistory_measurable M.toEuclideanSCM t.val _),
    Measure.map_map (by fun_prop) (approximationHistory_measurable N.toEuclideanSCM t.val _)] at h
  simpa only [Function.comp_def, approximationContinuousUpdate,
    ← approximationHistory_continuous_step_eq _ t.val i d hi ht] using h

end
end Papers.TbsNeuralCausalPi
