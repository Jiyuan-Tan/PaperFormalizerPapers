module
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseNonDescendant
/-! # Separation of descendant-private latent inputs

Restrict the named independent latent family to the strict descendants' inputs.
The complementary restriction suffices to evaluate the non-descendants and the
treatment. This realizes the noise separation in the adjustment roadmap.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- For [node types](hyp:kind) on [a finite set of nodes](hyp:n), [latent-block
dimensions](hyp:dims) for [a finite number of blocks](hyp:b), [a selected set
of named latent inputs](hyp:S), and [an exogenous vector](hyp:u), the
[restricted latent family](goal) keeps [coordinates of selected shared blocks,
setting the other shared-block coordinates to zero](step:1), and keeps
[coordinates of selected node-specific noise vectors, setting the other
node-specific coordinates to zero](step:2). -/
-- @node: restrictLatentFamily
def restrictLatentFamily (S : Finset (Fin b ⊕ Fin n))
    (u : Exogenous kind dims) : Exogenous kind dims :=
  WithLp.toLp 1 (fun c => match c with
    | .inl ⟨j,k⟩ => if Sum.inl j ∈ S then u.ofLp (.inl ⟨j,k⟩) else 0
    | .inr ⟨i,k⟩ => if Sum.inr i ∈ S then u.ofLp (.inr ⟨i,k⟩) else 0)

-- @node: restrictLatentFamily_measurable
/-- [Keeping a fixed selection of named latent inputs and replacing all
other coordinates by zero is a measurable transformation of the exogenous
vector](goal). -/
@[fun_prop] lemma restrictLatentFamily_measurable (S : Finset (Fin b ⊕ Fin n)) :
    Measurable (restrictLatentFamily (kind := kind) (dims := dims) S) := by
  first | fun_prop | skip
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  rintro (⟨j,k⟩ | ⟨i,k⟩) <;> dsimp <;> split_ifs <;> fun_prop

/-- If [the model's named latent inputs are jointly independent](hyp:hind)
and [two selections of those inputs are disjoint](hyp:hSR), then [the two
exogenous vectors obtained by keeping each selection and zeroing all other
coordinates are independent under the model's latent law](goal). -/
-- @node: restrictLatentFamily_indepFun
lemma restrictLatentFamily_indepFun (M : EuclideanSCM kind dims)
    (hind : LatentBlocksIndependent M) (S R : Finset (Fin b ⊕ Fin n))
    (hSR : Disjoint S R) :
    IndepFun (restrictLatentFamily (kind := kind) (dims := dims) S)
      (restrictLatentFamily R) M.latentLaw := by
  classical
  let restore (S : Finset (Fin b ⊕ Fin n))
      (w : ∀ j : S, L1Vec (fullLatentDim kind dims j.val)) : Exogenous kind dims :=
    WithLp.toLp 1 (fun c => match c with
      | .inl ⟨j,k⟩ => if h : Sum.inl j ∈ S then (w ⟨.inl j,h⟩).ofLp k else 0
      | .inr ⟨i,k⟩ => if h : Sum.inr i ∈ S then (w ⟨.inr i,h⟩).ofLp k else 0)
  have hm (S : Finset (Fin b ⊕ Fin n)) : Measurable (restore S) := by
    first | fun_prop | skip
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro (⟨j,k⟩ | ⟨i,k⟩) <;> dsimp [restore] <;> split_ifs <;> fun_prop
  have hn (j : Fin b ⊕ Fin n) : Measurable (namedLatent M j) := by
    first | fun_prop | skip
    cases j <;> fun_prop [namedLatent, blockProjection, categoricalNoise]
  have h := (iIndepFun.indepFun_finset S R hSR hind hn).comp (hm S) (hm R)
  have he (S : Finset (Fin b ⊕ Fin n)) :
      restore S ∘ (fun u j => namedLatent M j.val u) = restrictLatentFamily S := by
    funext u
    apply WithLp.ofLp_injective
    funext c
    rcases c with ⟨j,k⟩ | ⟨i,k⟩ <;>
      simp [restore, restrictLatentFamily, namedLatent, blockProjection, categoricalNoise]
  simpa only [he] using h

/-- For [a treatment node](hyp:T) among [a finite set of nodes](hyp:n),
[a directed acyclic graph](hyp:dag), and [the node memberships of latent
blocks](hyp:C) indexed by [a finite number of blocks](hyp:b), the
[descendant latent indices](goal) select [shared blocks incident to at least
one strict descendant of the treatment](step:1) and [node-specific noise
vectors belonging to strict descendants](step:2). -/
-- @node: descendantLatentIndices
def descendantLatentIndices (T : Fin n) : Finset (Fin b ⊕ Fin n) :=
  Finset.univ.filter (fun j => match j with
    | .inl k => ∃ i, i ≠ T ∧ dag.isAncestor T i ∧ k ∈ canonicalIncidence C i
    | .inr i => i ≠ T ∧ dag.isAncestor T i)

/-- If [there is no hidden confounding](hyp:hnoconf), [a node is the treatment
itself or is not its descendant](hyp:hi), and [a latent block enters that
node's mechanism](hyp:hk), then [that block is absent from the latent inputs
used by strict descendants of the treatment](goal). -/
-- @node: nonDescendant_block_not_mem_descendantLatentIndices
lemma nonDescendant_block_not_mem_descendantLatentIndices
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (T i : Fin n) (hi : i = T ∨ ¬ dag.isAncestor T i)
    (k : Fin b) (hk : k ∈ canonicalIncidence C i) :
    Sum.inl k ∉ descendantLatentIndices (dag := dag) (C := C) T := by
  simp only [descendantLatentIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨j, hjT, hj, hkj⟩
  have he := canonicalIncidence_node_unique M hnoconf hk hkj
  subst j
  rcases hi with hi | hi
  · exact hjT hi
  · exact hi hj

/-- [When the treatment is fixed at a chosen dose and all non-descendants
are fixed at their coordinates in a chosen joint vector, replacing the
exogenous vector by its restriction to strict-descendant latent inputs leaves
the entire simulated joint vector unchanged](goal). -/
-- @node: descendantEval_restrict_private_noise
lemma descendantEval_restrict_private_noise
    (M : CanonicalSCM kind dims dag G C) (T : Fin n)
    (a : Joint kind) (t : ℝ) (u : Exogenous kind dims) :
    let assignment : Intervention kind := fun i =>
      if i = T then some (WithLp.toLp 1 (fun _ => t)) else
        if i ∈ nonDescendantNodes (dag := dag) T then
          some (WithLp.toLp 1 (fun j => a.ofLp ⟨i,j⟩)) else none
    intervenedEval M.toEuclideanSCM assignment u =
      intervenedEval M.toEuclideanSCM assignment
        (restrictLatentFamily (descendantLatentIndices (dag := dag) (C := C) T) u) := by
  apply descendantEval_eq_of_private_noise_eq
  · intro i hi hp k hk j
    have hmem : Sum.inl k ∈ descendantLatentIndices (dag := dag) (C := C) T := by
      simp only [descendantLatentIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, hi, hp, hk⟩
    simp [restrictLatentFamily, hmem]
  · intro i hi hp
    have hmem : Sum.inr i ∈ descendantLatentIndices (dag := dag) (C := C) T := by
      simp [descendantLatentIndices, hi, hp]
    apply WithLp.ofLp_injective
    funext k
    simp [categoricalNoise, restrictLatentFamily, hmem]


/-- If [a set of nodes contains every parent of each of its members](hyp:hS),
[two exogenous vectors agree on every shared-block coordinate read by those
nodes](hyp:hb), and [they agree on those nodes' categorical noise vectors](hyp:hg),
then [under the same intervention the structural evaluations agree on every
coordinate of those nodes after any number of evaluation steps](goal). -/
-- @node: evalSteps_eq_on_parent_closed_of_noise_eq
lemma evalSteps_eq_on_parent_closed_of_noise_eq (M : EuclideanSCM kind dims)
    (S : Set (Fin n)) (hS : ∀ i ∈ S, ∀ p ∈ M.dag.parents i, p ∈ S)
    (t : Intervention kind) (u u' : Exogenous kind dims)
    (hb : ∀ i ∈ S, ∀ k ∈ M.incidence i, ∀ j,
      u.ofLp (.inl ⟨k,j⟩) = u'.ofLp (.inl ⟨k,j⟩))
    (hg : ∀ i ∈ S, categoricalNoise i u = categoricalNoise i u') (r : ℕ) :
    ∀ i ∈ S, ∀ j, (evalSteps M t u r).ofLp ⟨i,j⟩ =
      (evalSteps M t u' r).ofLp ⟨i,j⟩ := by
  induction r with
  | zero => intro i hi j; rfl
  | succ r ih =>
    intro i hi j
    have hx : structuralInput M i (evalSteps M t u r) u =
        structuralInput M i (evalSteps M t u' r) u' := by
      apply WithLp.ofLp_injective
      funext c
      rcases c with ⟨p,k⟩ | ⟨k,l⟩
      · exact ih p.val (hS i hi p.val p.property) k
      · exact hb i hi k.val k.property l
    have hn : nodeValue M i (evalSteps M t u r) u =
        nodeValue M i (evalSteps M t u' r) u' := by
      unfold nodeValue
      rw [hx, hg i hi]
    simp only [evalSteps, WithLp.ofLp_toLp]
    split_ifs
    · rw [hn]
    · exact ih i hi j

/-- If [there is no hidden confounding](hyp:hnoconf) and [a node is not a
descendant of the treatment](hyp:hi), then [each of that node's observational
coordinates is unchanged when the latent inputs used by strict descendants
are replaced by zero](goal). -/
-- @node: nonDescendantEval_restrict_complement_noise
lemma nonDescendantEval_restrict_complement_noise
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (T : Fin n) (u : Exogenous kind dims) (i : Fin n)
    (hi : ¬ dag.isAncestor T i) (j : Fin (valueDim (kind i))) :
    (intervenedEval M.toEuclideanSCM (fun _ => none) u).ofLp ⟨i,j⟩ =
      (intervenedEval M.toEuclideanSCM (fun _ => none)
        (restrictLatentFamily (descendantLatentIndices (dag := dag) (C := C) T)ᶜ u)).ofLp ⟨i,j⟩ := by
  apply evalSteps_eq_on_parent_closed_of_noise_eq M.toEuclideanSCM
    {i | ¬ dag.isAncestor T i} _ (fun _ => none) u
    (restrictLatentFamily (descendantLatentIndices (dag := dag) (C := C) T)ᶜ u) _ _
    (n*n+n) i hi j
  · intro i hi p hp hpath
    exact hi (.trans hpath (dag.mem_parents.mp hp))
  · intro i hi k hk j
    have hk' := nonDescendant_block_not_mem_descendantLatentIndices M hnoconf T i
      (Or.inr hi) k hk
    simp [restrictLatentFamily, hk']
  · intro i hi
    have hi' : Sum.inr i ∉ descendantLatentIndices (dag := dag) (C := C) T := by
      simp only [descendantLatentIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun h => hi h.2
    apply WithLp.ofLp_injective
    funext k
    simp [categoricalNoise, restrictLatentFamily, hi']

/-- If [there is no hidden confounding](hyp:hnoconf), [the named latent
inputs are jointly independent](hyp:hind), and [the treatment is scalar](hyp:hT),
then [the pair consisting of the observed non-descendant vector and observed
treatment is independent of the exogenous vector restricted to the latent
inputs of strict descendants](goal). -/
-- @node: nonDescendant_treatment_indep_private_noise
lemma nonDescendant_treatment_indep_private_noise
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (hind : LatentBlocksIndependent M.toEuclideanSCM)
    (T : Fin n) (hT : valueDim (kind T) = 1) :
    IndepFun (fun u =>
      (nonDescendantProjection (dag := dag) T
        (intervenedEval M.toEuclideanSCM (fun _ => none) u),
       scalarOutcome T hT (intervenedEval M.toEuclideanSCM (fun _ => none) u)))
      (restrictLatentFamily (descendantLatentIndices (dag := dag) (C := C) T))
      M.latentLaw := by
  let S := descendantLatentIndices (dag := dag) (C := C) T
  let F : Exogenous kind dims → Joint kind × ℝ := fun u =>
    (nonDescendantProjection (dag := dag) T
      (intervenedEval M.toEuclideanSCM (fun _ => none) u),
     scalarOutcome T hT (intervenedEval M.toEuclideanSCM (fun _ => none) u))
  have hev : Measurable (intervenedEval M.toEuclideanSCM (fun _ => none)) :=
    evalSteps_measurable M.toEuclideanSCM _ _
  have hm : Measurable F := by
    first | fun_prop | skip
    apply Measurable.prodMk
    · apply scm_toLp_measurable.comp
      apply measurable_pi_lambda
      rintro ⟨i,j⟩
      dsimp [nonDescendantProjection]
      split_ifs <;> fun_prop
    · fun_prop [scalarOutcome]
  have he : F ∘ restrictLatentFamily Sᶜ = F := by
    funext u
    apply Prod.ext
    · apply WithLp.ofLp_injective
      funext ⟨i,j⟩
      dsimp [F, nonDescendantProjection]
      split_ifs with hi
      · have hp : ¬ dag.isAncestor T i := by
          exact (Finset.mem_filter.mp hi).2.2
        exact (nonDescendantEval_restrict_complement_noise M hnoconf T u i hp j).symm
      · rfl
    · exact (nonDescendantEval_restrict_complement_noise M hnoconf T u T
        (dag.isAncestor_irrefl T) _).symm
  have h := (restrictLatentFamily_indepFun M.toEuclideanSCM hind Sᶜ S
    (by exact disjoint_compl_left)).comp hm measurable_id
  change IndepFun F (restrictLatentFamily S) M.toEuclideanSCM.latentLaw
  simpa only [he, Function.id_comp] using h


/-- If [the treatment is scalar](hyp:hT), then [fixing the treatment and
non-descendants at their observed values and simulating with only the
strict-descendant latent inputs reproduces the full observed joint vector
for every exogenous realization](goal). -/
-- @node: observationalEval_descendant_noise_factorization
lemma observationalEval_descendant_noise_factorization
    (M : CanonicalSCM kind dims dag G C) (T : Fin n)
    (hT : valueDim (kind T) = 1) (u : Exogenous kind dims) :
    let v := intervenedEval M.toEuclideanSCM (fun _ => none) u
    intervenedEval M.toEuclideanSCM
      (fun i => if i = T then some (WithLp.toLp 1 (fun _ => scalarOutcome T hT v)) else
        if i ∈ nonDescendantNodes (dag := dag) T then
          some (WithLp.toLp 1 (fun j =>
            (nonDescendantProjection (dag := dag) T v).ofLp ⟨i,j⟩)) else none)
      (restrictLatentFamily (descendantLatentIndices (dag := dag) (C := C) T) u) = v := by
  exact (descendantEval_restrict_private_noise M T _ _ u).symm.trans
    (descendantEval_eq_observational M T hT u)

/-- If [the outcome is scalar](hyp:hY), then [the descendant mean at any
chosen joint vector and treatment dose equals the expected simulated outcome
when treatment and non-descendants are fixed accordingly and the exogenous
vector is drawn from the law restricted to strict-descendant latent inputs](goal). -/
-- @node: descendantMean_eq_integral_private_noise
lemma descendantMean_eq_integral_private_noise
    (M : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hY : valueDim (kind Y) = 1) (a : Joint kind) (t : ℝ) :
    descendantMean M T Y hY a t =
      ∫ u, scalarOutcome Y hY (intervenedEval M.toEuclideanSCM
        (fun i => if i = T then some (WithLp.toLp 1 (fun _ => t)) else
          if i ∈ nonDescendantNodes (dag := dag) T then
            some (WithLp.toLp 1 (fun j => a.ofLp ⟨i,j⟩)) else none) u)
        ∂(M.latentLaw.map (restrictLatentFamily
          (descendantLatentIndices (dag := dag) (C := C) T))) := by
  have hm : Measurable (fun u => scalarOutcome Y hY
      (intervenedEval M.toEuclideanSCM
        (fun i => if i = T then some (WithLp.toLp 1 (fun _ => t)) else
          if i ∈ nonDescendantNodes (dag := dag) T then
            some (WithLp.toLp 1 (fun j => a.ofLp ⟨i,j⟩)) else none) u)) := by
    first | fun_prop | skip
    have he : Measurable (intervenedEval M.toEuclideanSCM
        (fun i => if i = T then some (WithLp.toLp 1 (fun _ => t)) else
          if i ∈ nonDescendantNodes (dag := dag) T then
            some (WithLp.toLp 1 (fun j => a.ofLp ⟨i,j⟩)) else none)) :=
      evalSteps_measurable M.toEuclideanSCM _ _
    fun_prop [scalarOutcome]
  rw [integral_map (restrictLatentFamily_measurable _).aemeasurable
    hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u =>
    congrArg (scalarOutcome Y hY) (descendantEval_restrict_private_noise M T a t u)

end
end Papers.TbsNeuralCausalPi
