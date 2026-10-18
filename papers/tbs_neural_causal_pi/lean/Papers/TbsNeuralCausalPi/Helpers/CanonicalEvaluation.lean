module
public import Papers.TbsNeuralCausalPi.Helpers.CanonicalLatentLaw
public import Papers.TbsNeuralCausalPi.Helpers.DescendantNoise
public import Papers.TbsNeuralCausalPi.Helpers.InterventionDomains
/-! # Synchronous evaluation under canonical regrouping

A history before a node's visit ignores that node's intrinsic Gumbels, even
when non-Gumbel blocks are shared. This separates the random structural input
from the fresh Gumbels without imposing absence of hidden confounding.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

/-- For [a Euclidean causal model](hyp:M), [a node](hyp:i), [an intervention](hyp:t),
[an exogenous realization](hyp:u), and [an evaluation step](hyp:r), if
[that step is no later than the node's position in the topological order](hyp:hr),
then [setting only that node's intrinsic noise to zero leaves the evaluated
history unchanged](goal). -/
-- @node: evalSteps_erase_current_gumbels
lemma evalSteps_erase_current_gumbels (M : EuclideanSCM kind dims)
    (i : Fin n) (t : Intervention kind) (u : Exogenous kind dims)
    (r : ℕ) (hr : r ≤ M.dag.topoOrder i) :
    evalSteps M t u r = evalSteps M t
      (restrictLatentFamily ({Sum.inr i} : Finset (Fin b ⊕ Fin n))ᶜ u) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hp := ih (by omega)
    apply WithLp.ofLp_injective
    funext ⟨j,k⟩
    simp only [evalSteps, WithLp.ofLp_toLp]
    by_cases hj : M.dag.topoOrder j = r
    · have hji : j ≠ i := by intro he; subst j; omega
      have hx : structuralInput M j (evalSteps M t u r) u =
          structuralInput M j (evalSteps M t
            (restrictLatentFamily ({Sum.inr i} : Finset (Fin b ⊕ Fin n))ᶜ u) r)
            (restrictLatentFamily ({Sum.inr i} : Finset (Fin b ⊕ Fin n))ᶜ u) := by
        rw [hp]
        apply WithLp.ofLp_injective
        funext c
        rcases c with ⟨p,l⟩ | ⟨a,l⟩
        · rfl
        · change u.ofLp (.inl ⟨a.val,l⟩) =
            if Sum.inl a.val ∈ ({Sum.inr i} : Finset (Fin b ⊕ Fin n))ᶜ then
              u.ofLp (.inl ⟨a.val,l⟩) else 0
          simp only [Finset.mem_compl, Finset.mem_singleton, Sum.inl_ne_inr,
            not_false_eq_true, if_true]
      have hg : categoricalNoise j u = categoricalNoise j
          (restrictLatentFamily ({Sum.inr i} : Finset (Fin b ⊕ Fin n))ᶜ u) := by
        apply WithLp.ofLp_injective
        funext l
        change u.ofLp (.inr ⟨j,l⟩) =
          if Sum.inr j ∈ ({Sum.inr i} : Finset (Fin b ⊕ Fin n))ᶜ then
            u.ofLp (.inr ⟨j,l⟩) else 0
        simp only [Finset.mem_compl, Finset.mem_singleton, Sum.inr.injEq, hji,
          not_false_eq_true, if_true]
      have hn : nodeValue M j (evalSteps M t u r) u = nodeValue M j
          (evalSteps M t (restrictLatentFamily
            ({Sum.inr i} : Finset (Fin b ⊕ Fin n))ᶜ u) r)
          (restrictLatentFamily ({Sum.inr i} : Finset (Fin b ⊕ Fin n))ᶜ u) := by
        unfold nodeValue
        rw [hx, hg]
      simp only [hj, if_true]
      rw [hn]
    · simp only [hj, if_false]
      exact congrArg (fun v : Joint kind => v.ofLp ⟨j,k⟩) hp

/-- For [a Euclidean causal model](hyp:M), [a node](hyp:i), [an intervention](hyp:t),
and [an exogenous realization](hyp:u), [setting the node's intrinsic noise
to zero in both the preceding evaluation and the exogenous input leaves
its structural input at its topological visit unchanged](goal). -/
-- @node: structuralInput_evalSteps_erase_current_gumbels
lemma structuralInput_evalSteps_erase_current_gumbels (M : EuclideanSCM kind dims)
    (i : Fin n) (t : Intervention kind) (u : Exogenous kind dims) :
    structuralInput M i (evalSteps M t u (M.dag.topoOrder i)) u =
      structuralInput M i (evalSteps M t
        (restrictLatentFamily ({Sum.inr i} : Finset (Fin b ⊕ Fin n))ᶜ u)
          (M.dag.topoOrder i))
        (restrictLatentFamily ({Sum.inr i} : Finset (Fin b ⊕ Fin n))ᶜ u) := by
  rw [evalSteps_erase_current_gumbels M i t u _ le_rfl]
  apply WithLp.ofLp_injective
  funext c
  rcases c with ⟨p,l⟩ | ⟨a,l⟩
  · rfl
  · change u.ofLp (.inl ⟨a.val,l⟩) =
      if Sum.inl a.val ∈ ({Sum.inr i} : Finset (Fin b ⊕ Fin n))ᶜ then
        u.ofLp (.inl ⟨a.val,l⟩) else 0
    simp only [Finset.mem_compl, Finset.mem_singleton, Sum.inl_ne_inr,
      not_false_eq_true, if_true]

/-- For [a Euclidean causal model](hyp:M) whose [named latent blocks are
independent](hyp:hind), fix [a node](hyp:i), [an intervention](hyp:t), and
[a category count](hyp:k) with [the node categorical of that size](hyp:hi).
Then [the node's structural input at its topological visit is independent
of its reindexed intrinsic Gumbel vector under the model's latent law](goal). -/
-- @node: structuralInput_evalSteps_indep_current_gumbels
lemma structuralInput_evalSteps_indep_current_gumbels (M : EuclideanSCM kind dims)
    (hind : LatentBlocksIndependent M) (i : Fin n) (t : Intervention kind)
    (k : ℕ) (hi : kind i = Sum.inr k) :
    IndepFun (fun u => structuralInput M i (evalSteps M t u (M.dag.topoOrder i)) u)
      (fun u (l : Fin k) => (categoricalNoise i u).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l)) M.latentLaw := by
  let S : Finset (Fin b ⊕ Fin n) := {Sum.inr i}
  let X := fun u => structuralInput M i (evalSteps M t u (M.dag.topoOrder i)) u
  let g := fun (u : Exogenous kind dims) (l : Fin k) => (categoricalNoise i u).ofLp
    (Fin.cast (congrArg noiseDim hi).symm l)
  have hX : Measurable X := by fun_prop
  have hg : Measurable g := by fun_prop
  have heX : X ∘ restrictLatentFamily Sᶜ = X := by
    funext u
    exact (structuralInput_evalSteps_erase_current_gumbels M i t u).symm
  have heg : g ∘ restrictLatentFamily S = g := by
    funext u l
    change (if Sum.inr i ∈ S then _ else 0) = _
    simp only [S, Finset.mem_singleton_self, if_true]
    rfl
  have h := (restrictLatentFamily_indepFun M hind Sᶜ S disjoint_compl_left).comp hX hg
  simpa only [heX, heg] using h

/-- For [a Euclidean causal model](hyp:M) and [mechanism weights](hyp:p)
[satisfying the Gumbel argmax assumptions](hyp:hcat), fix [a node](hyp:i) and
[a category count](hyp:k) with [the node categorical of that size](hyp:hi).
Suppose [a random structural input](hyp:X) [is measurable](hyp:hX),
[always lies in the declared domain](hyp:hd), and [is independent of the
node's actual intrinsic Gumbels](hyp:hind), and suppose [a weight map](hyp:w)
[is measurable](hyp:hw) and [equals the mechanism weights divided by their
sum on the domain](hyp:hwn). Then [the actual categorical label at that
input equals almost surely the canonical selector using those normalized
weights and the same intrinsic Gumbels](goal). -/
-- @node: categoricalLabel_random_input_ae_normalized
lemma categoricalLabel_random_input_ae_normalized
    (M : EuclideanSCM kind dims) (p : MechanismWeights M)
    (hcat : CategoricalGumbelArgmax M p) (i : Fin n) (k : ℕ)
    (hi : kind i = Sum.inr k)
    (X : Exogenous kind dims → StructuralInput kind dims M.dag M.incidence i)
    (hX : Measurable X) (hd : ∀ u, X u ∈ M.domain i)
    (hind : IndepFun X (fun u (l : Fin k) => (categoricalNoise i u).ofLp
      (Fin.cast (congrArg noiseDim hi).symm l)) M.latentLaw)
    (w : StructuralInput kind dims M.dag M.incidence i → L1Vec (outputDim (kind i)))
    (hw : Measurable w)
    (hwn : ∀ x ∈ M.domain i,
      w x = WithLp.toLp 1 (fun j => (p i x).ofLp j / ∑ l, (p i x).ofLp l)) :
    (fun u => M.categoricalLabel i k hi (X u)
      (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l)))) =ᵐ[M.latentLaw]
    (fun u => canonicalSelector (.inr k)
      (fun m hm => M.categoricalPositive i m (hi.trans hm))
      (WithLp.toLp 1 (fun j => (w (X u)).ofLp
        (Fin.cast (congrArg outputDim hi).symm j)))
      (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l)))) := by
  let := M.probability
  let g := fun (u : Exogenous kind dims) (l : Fin k) =>
    (categoricalNoise i u).ofLp (Fin.cast (congrArg noiseDim hi).symm l)
  let F := fun z : StructuralInput kind dims M.dag M.incidence i × (Fin k → ℝ) =>
    M.categoricalLabel i k hi z.1 (WithLp.toLp 1 z.2)
  let H := fun z : StructuralInput kind dims M.dag M.incidence i × (Fin k → ℝ) =>
    canonicalSelector (.inr k)
      (fun m hm => M.categoricalPositive i m (hi.trans hm))
      (WithLp.toLp 1 (fun j => (w z.1).ofLp
        (Fin.cast (congrArg outputDim hi).symm j))) (WithLp.toLp 1 z.2)
  have hF : Measurable F := by fun_prop
  have hH : Measurable H := by
    apply firstArgmax_getD_measurable
    intro j
    fun_prop
  have hg : Measurable g := by fun_prop
  have hjoint : M.latentLaw.map (fun u => (X u, g u)) =
      (M.latentLaw.map X).prod (gumbelInputs k) := by
    rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hg.aemeasurable]
    exact congrArg ((M.latentLaw.map X).prod) (hcat.2.2.2 i k hi)
  have he : F =ᵐ[(M.latentLaw.map X).prod (gumbelInputs k)] H := by
    let := gumbelInputs_probability k
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hF hH)).2
    have hx : ∀ᵐ x ∂M.latentLaw.map X, x ∈ M.domain i :=
      (ae_map_iff hX.aemeasurable (M.domain_measurableSet i)).2
        (Filter.Eventually.of_forall hd)
    filter_upwards [hx] with x hx
    have hn := categoricalLabel_ae_normalized_selector M p hcat i k hi x hx
    filter_upwards [hn] with a ha
    simpa only [F, H, hwn x hx, WithLp.ofLp_toLp] using ha
  rw [← hjoint] at he
  exact (ae_map_iff (hX.prodMk hg).aemeasurable
    (measurableSet_eq_fun hF hH)).1 he

/-- For [a Euclidean causal model](hyp:M), [a node](hyp:i), and
[a category count](hyp:k) with [the node categorical of that size](hyp:hi),
at [a structural input](hyp:x) and [an exogenous realization](hyp:u),
[the categorical label computed from the reindexed actual noise equals
the original structural output expressed as a category](goal). -/
-- @node: categoricalLabel_actual_noise
lemma categoricalLabel_actual_noise (M : EuclideanSCM kind dims)
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    (x : StructuralInput kind dims M.dag M.incidence i) (u : Exogenous kind dims) :
    M.categoricalLabel i k hi x
      (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
        (Fin.cast (congrArg noiseDim hi).symm l))) =
      cast (congrArg ObservedValue hi) (M.f i x (categoricalNoise i u)) := by
  unfold EuclideanSCM.categoricalLabel
  congr 2

/-- For [a Euclidean causal model](hyp:M), [a node](hyp:i), and
[a continuous dimension](hyp:d) with [the node continuous of that dimension](hyp:hi),
given [an observed history](hyp:v), [an exogenous realization](hyp:u), and
[an observed coordinate](hyp:j), [that coordinate of the node value equals
the corresponding coordinate of its continuous structural map at the
induced structural input](goal). -/
-- @node: nodeValue_continuousMap_coordinate
lemma nodeValue_continuousMap_coordinate (M : EuclideanSCM kind dims)
    (i : Fin n) (d : ℕ) (hi : kind i = Sum.inl d)
    (v : Joint kind) (u : Exogenous kind dims) (j : Fin (valueDim (kind i))) :
    (nodeValue M i v u).ofLp j =
      (M.continuousMap i (structuralInput M i v u)).ofLp
        (Fin.cast ((congrArg valueDim hi).trans (congrArg outputDim hi).symm) j) := by
  haveI : Subsingleton (L1Vec (noiseDim (kind i))) := by
    rw [hi]
    change Subsingleton (L1Vec 0)
    infer_instance
  have hg : categoricalNoise i u = 0 := Subsingleton.elim _ _
  have h (κ : NodeKind) (hκ : κ = .inl d) (y : ObservedValue κ)
      (l : Fin (valueDim κ)) :
      (observedValueEmbedding κ y).ofLp l =
        (show L1Vec (outputDim (id κ)) from match h : id κ with
        | .inl _ => WithLp.toLp 1 (fun j => (cast (congrArg ObservedValue h) y).ofLp j)
        | .inr _ => 0).ofLp
          (Fin.cast ((congrArg valueDim hκ).trans (congrArg outputDim hκ).symm) l) := by
    subst κ
    rfl
  rw [show nodeValue M i v u = _ from (observedValueEmbedding_eq _ _).symm, hg]
  exact h (kind i) hi (M.f i (structuralInput M i v u) 0) j

/-- For [a canonical causal model](hyp:N), [a node](hyp:i), and
[a continuous dimension](hyp:d) with [the node continuous of that dimension](hyp:hi),
at [a structural input](hyp:x), [the continuous mechanism equals the
canonical structural weight map](goal). -/
-- @node: canonical_continuousMap_eq_weights
lemma canonical_continuousMap_eq_weights {b' : ℕ} {dims' : Fin b' → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b' → Set (Fin n)} (N : CanonicalSCM kind dims' dag G C)
    (i : Fin n) (d : ℕ) (hi : kind i = Sum.inl d)
    (x : StructuralInput kind dims' dag (canonicalIncidence C) i) :
    N.toEuclideanSCM.continuousMap i x = N.f i x := by
  have h (κ : NodeKind) (hκ : κ = .inl d)
      (hk : ∀ m, κ = .inr m → 0 < m) (w : L1Vec (outputDim κ)) :
      (show L1Vec (outputDim (id κ)) from match h : id κ with
      | .inl _ => WithLp.toLp 1 (fun j =>
          (cast (congrArg ObservedValue h) (canonicalSelector κ hk w 0)).ofLp j)
      | .inr _ => 0) = w := by
    subst κ
    rfl
  unfold EuclideanSCM.continuousMap
  change (show L1Vec (outputDim (kind i)) from match h : kind i with
    | .inl _ => WithLp.toLp 1 (fun j =>
        (cast (congrArg ObservedValue h) (canonicalMechanism N i x 0)).ofLp j)
    | .inr _ => 0) = _
  rw [show canonicalMechanism N i x 0 =
    canonicalSelector (kind i) (N.positive_categories i) (N.f i x) 0 from
      (canonicalSelector_eq _ _ _ _).symm]
  exact h (kind i) hi (N.positive_categories i) (N.f i x)

/-- For [two Euclidean causal models](hyp:M,N), [a node](hyp:i), and
[a category count](hyp:k) with [the node categorical of that size](hyp:hi),
fix [a common observed history](hyp:v) and [exogenous realizations for the
two models](hyp:u,u'). If [the categorical labels at the induced inputs
and actual intrinsic noises agree](hyp:he), then [the two embedded node
values agree](goal). -/
-- @node: nodeValue_eq_of_categoricalLabel_eq
lemma nodeValue_eq_of_categoricalLabel_eq {b' : ℕ} {dims' : Fin b' → ℕ}
    (M : EuclideanSCM kind dims) (N : EuclideanSCM kind dims')
    (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    (v : Joint kind) (u : Exogenous kind dims) (u' : Exogenous kind dims')
    (he : M.categoricalLabel i k hi (structuralInput M i v u)
        (WithLp.toLp 1 (fun l => (categoricalNoise i u).ofLp
          (Fin.cast (congrArg noiseDim hi).symm l))) =
      N.categoricalLabel i k hi (structuralInput N i v u')
        (WithLp.toLp 1 (fun l => (categoricalNoise i u').ofLp
          (Fin.cast (congrArg noiseDim hi).symm l)))) :
    nodeValue M i v u = nodeValue N i v u' := by
  rw [categoricalLabel_actual_noise, categoricalLabel_actual_noise] at he
  have h (κ : NodeKind) (hκ : κ = .inr k) (a b : ObservedValue κ)
      (hab : cast (congrArg ObservedValue hκ) a = cast (congrArg ObservedValue hκ) b) :
      observedValueEmbedding κ a = observedValueEmbedding κ b := by
    subst κ
    exact congrArg (observedValueEmbedding (.inr k)) hab
  exact (observedValueEmbedding_eq _ _).symm.trans
    ((h _ hi _ _ he).trans (observedValueEmbedding_eq _ _))

/-- For [two Euclidean causal models](hyp:M,N) with [the same directed
acyclic graph](hyp:hdag), [a map between their exogenous spaces](hyp:merge),
and [a common intervention](hyp:t), suppose [each node's value agrees
almost surely between the models at the first model's history just before
that node's visit, using the mapped exogenous realization in the second
model](hyp:hnode). Then at [any evaluation step](hyp:r), [the two evaluated
histories agree almost surely under the first model's latent law](goal). -/
-- @node: evalSteps_regrouped_ae_of_nodeValue_ae
lemma evalSteps_regrouped_ae_of_nodeValue_ae {b' : ℕ} {dims' : Fin b' → ℕ}
    (M : EuclideanSCM kind dims) (N : EuclideanSCM kind dims')
    (hdag : N.dag = M.dag) (merge : Exogenous kind dims → Exogenous kind dims')
    (t : Intervention kind)
    (hnode : ∀ i, ∀ᵐ u ∂M.latentLaw,
      nodeValue M i (evalSteps M t u (M.dag.topoOrder i)) u =
        nodeValue N i (evalSteps M t u (M.dag.topoOrder i)) (merge u))
    (r : ℕ) :
    (fun u => evalSteps M t u r) =ᵐ[M.latentLaw]
      (fun u => evalSteps N t (merge u) r) := by
  have hall : ∀ᵐ u ∂M.latentLaw, ∀ i,
      nodeValue M i (evalSteps M t u (M.dag.topoOrder i)) u =
        nodeValue N i (evalSteps M t u (M.dag.topoOrder i)) (merge u) :=
    (ae_all_iff).2 hnode
  induction r with
  | zero => exact Filter.Eventually.of_forall fun _ => rfl
  | succ r ih =>
    filter_upwards [ih, hall] with u hu hn
    apply WithLp.ofLp_injective
    funext ⟨i,j⟩
    simp only [evalSteps, WithLp.ofLp_toLp, hdag]
    by_cases hi : M.dag.topoOrder i = r
    · simp only [hi, if_true]
      have he := hn i
      rw [hi] at he
      rw [← hu, he]
    · simp only [hi, if_false]
      exact congrArg (fun v : Joint kind => v.ofLp ⟨i,j⟩) hu

/-- For [two Euclidean causal models](hyp:M,N) with [the same directed
acyclic graph](hyp:hdag), suppose [a map between their exogenous spaces](hyp:merge)
[is measurable](hyp:hm) and [pushes the first latent law forward to the
second](hyp:hlaw). For [a common admissible intervention](hyp:t), if
[each node's value agrees almost surely between the models at the first
model's history just before that node's visit, using the mapped exogenous
realization in the second](hyp:hnode), then [the two interventional laws
are equal](goal). -/
-- @node: interventionalLaw_regrouped_of_nodeValue_ae
lemma interventionalLaw_regrouped_of_nodeValue_ae {b' : ℕ} {dims' : Fin b' → ℕ}
    (M : EuclideanSCM kind dims) (N : EuclideanSCM kind dims')
    (hdag : N.dag = M.dag) (merge : Exogenous kind dims → Exogenous kind dims')
    (hm : Measurable merge) (hlaw : N.latentLaw = M.latentLaw.map merge)
    (t : LawIntervention kind)
    (hnode : ∀ i, ∀ᵐ u ∂M.latentLaw,
      nodeValue M i (evalSteps M t.val u (M.dag.topoOrder i)) u =
        nodeValue N i (evalSteps M t.val u (M.dag.topoOrder i)) (merge u)) :
    interventionalLaw M t = interventionalLaw N t := by
  unfold interventionalLaw intervenedEval
  rw [hlaw, Measure.map_map (evalSteps_measurable N t.val _) hm]
  exact Measure.map_congr
    (evalSteps_regrouped_ae_of_nodeValue_ae M N hdag merge t.val hnode _)

end
end Papers.TbsNeuralCausalPi
