module
public import Papers.TbsNeuralCausalPi.Helpers.IndependentOverlap
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseMarginals
/-! # Treatment overlap on the full non-descendant covariate vector

Non-descendants use none of the treatment's private noise. The treatment
mechanism depends on this covariate vector only through its observed parents.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.unusedVariables false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

/-- If [i is an observed parent of the treatment T](hyp:hi), then
[i belongs to the treatment's non-descendant node set](goal). -/
-- @node: treatment_parent_mem_nonDescendantNodes
lemma treatment_parent_mem_nonDescendantNodes (T i : Fin n) (hi : i ∈ dag.parents T) :
    i ∈ nonDescendantNodes (dag := dag) T := by
  have he := dag.mem_parents.mp hi
  simp only [nonDescendantNodes, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    subst i
    exact dag.isAncestor_irrefl T (.edge he)
  · intro h
    exact dag.isAncestor_irrefl T (.trans h he)

/-- [Projecting a joint observation onto the treatment's non-descendants
preserves its vector of observed treatment-parent values](goal). -/
-- @node: parentValues_nonDescendantProjection
lemma parentValues_nonDescendantProjection (M : EuclideanSCM kind dims) (T : Fin n)
    (v : Joint kind) :
    parentValues M T (nonDescendantProjection (dag := M.dag) T v) = parentValues M T v := by
  apply WithLp.ofLp_injective
  funext ⟨i,j⟩
  simp only [parentValues, nonDescendantProjection, WithLp.ofLp_toLp,
    treatment_parent_mem_nonDescendantNodes T i.val i.property, if_true]

/-- If [there is no hidden confounding](hyp:hnoconf) and [the model's latent
blocks are independent](hyp:hind), then [the factual non-descendant vector
is independent of the latent noise used by the treatment mechanism under
the model's latent law](goal). -/
-- @node: nonDescendant_indep_treatment_noise
lemma nonDescendant_indep_treatment_noise
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    (hind : LatentBlocksIndependent M.toEuclideanSCM) (T : Fin n) :
    IndepFun (fun u => nonDescendantProjection (dag := dag) T
      (intervenedEval M.toEuclideanSCM (fun _ => none) u))
      (restrictLatentFamily (nodeLatentIndices (C := C) T)) M.latentLaw := by
  let S := nodeLatentIndices (C := C) T
  let A : Exogenous kind dims → Joint kind := fun u => nonDescendantProjection (dag := dag) T
    (intervenedEval M.toEuclideanSCM (fun _ => none) u)
  have hm : Measurable A := by
    first | fun_prop | skip
    exact (nonDescendantProjection_measurable T).comp (evalSteps_measurable M.toEuclideanSCM _ _)
  have he : A ∘ restrictLatentFamily Sᶜ = A := by
    funext u
    have hev := evalSteps_eq_on_parent_closed_of_noise_eq M.toEuclideanSCM
      {i | i ≠ T ∧ ¬ dag.isAncestor T i} ?_ (fun _ => none) u
      (restrictLatentFamily Sᶜ u) ?_ ?_ (n*n+n)
    · apply WithLp.ofLp_injective
      funext ⟨i,j⟩
      dsimp [A, nonDescendantProjection]
      split_ifs with hi
      · exact (hev i (Finset.mem_filter.mp hi).2 j).symm
      · rfl
    · intro i hi p hp
      have he := dag.mem_parents.mp hp
      refine ⟨?_, ?_⟩
      · intro h; subst p; exact hi.2 (.edge he)
      · intro h; exact hi.2 (.trans h he)
    · intro i hi k hk j
      have hki : k ∉ canonicalIncidence C T := by
        intro hkT
        exact hi.1 (canonicalIncidence_node_unique M hnoconf hk hkT)
      have hkS : Sum.inl k ∉ S := by
        simpa only [S, nodeLatentIndices, Finset.mem_filter, Finset.mem_univ, true_and] using hki
      simp [restrictLatentFamily, hkS]
    · intro i hi
      have hiS : Sum.inr i ∉ S := by
        simpa only [S, nodeLatentIndices, Finset.mem_filter, Finset.mem_univ, true_and] using hi.1
      apply WithLp.ofLp_injective
      funext j
      simp [categoricalNoise, restrictLatentFamily, hiS]
  have h := (restrictLatentFamily_indepFun M.toEuclideanSCM hind Sᶜ S
    disjoint_compl_left).comp hm measurable_id
  change IndepFun A (restrictLatentFamily S) M.toEuclideanSCM.latentLaw
  simpa only [he, Function.id_comp] using h

/-- Given [a structural causal model M](hyp:M), [a treatment node T](hyp:T),
and [a vector x of its observed parent values](hyp:x), the [reconstructed
joint vector](goal) assigns those values to the treatment's parent coordinates
and zero to every other coordinate. -/
-- @node: treatmentParentJoint
def treatmentParentJoint (M : EuclideanSCM kind dims) (T : Fin n)
    (x : ParentSpace M T) : Joint kind :=
  WithLp.toLp 1 (fun ⟨i,j⟩ => if hi : i ∈ M.dag.parents T then
    x.ofLp ⟨⟨i,hi⟩,j⟩ else 0)

-- @node: treatmentParentJoint_measurable
/-- [Reconstructing a joint vector from treatment-parent values by filling
all other coordinates with zero is a measurable map](goal). -/
@[fun_prop] lemma treatmentParentJoint_measurable (M : EuclideanSCM kind dims) (T : Fin n) :
    Measurable (treatmentParentJoint M T) := by
  first | fun_prop | skip
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  rintro ⟨i,j⟩
  dsimp [treatmentParentJoint]
  split_ifs <;> fun_prop

/-- If [two joint observations have the same observed parent values for node
i](hyp:h), then [the node mechanism gives the same value for both observations
when evaluated with the same exogenous noise](goal). -/
-- @node: nodeValue_eq_of_parentValues_eq
lemma nodeValue_eq_of_parentValues_eq (M : EuclideanSCM kind dims) (i : Fin n)
    (v w : Joint kind) (u : Exogenous kind dims)
    (h : parentValues M i v = parentValues M i w) :
    nodeValue M i v u = nodeValue M i w u := by
  have hx : structuralInput M i v u = structuralInput M i w u := by
    apply WithLp.ofLp_injective
    funext c
    rcases c with ⟨p,j⟩ | ⟨k,j⟩
    · exact congrArg (fun x : ParentSpace M i => x.ofLp ⟨p,j⟩) h
    · rfl
  unfold nodeValue
  rw [hx]

/-- [Each coordinate of the factual treatment value equals the corresponding
coordinate produced by its node mechanism using the completed factual
observation and the same exogenous noise](goal). -/
-- @node: observational_treatment_eq_nodeValue
lemma observational_treatment_eq_nodeValue (M : EuclideanSCM kind dims) (T : Fin n)
    (u : Exogenous kind dims) (j : Fin (valueDim (kind T))) :
    (intervenedEval M (fun _ => none) u).ofLp ⟨T,j⟩ =
      (nodeValue M T (intervenedEval M (fun _ => none) u) u).ofLp j := by
  have hp : parentValues M T (evalSteps M (fun _ => none) u (M.dag.topoOrder T)) =
      parentValues M T (intervenedEval M (fun _ => none) u) := by
    apply WithLp.ofLp_injective
    funext ⟨p,k⟩
    exact evalSteps_coordinate_eq_intervenedEval M _ u p.val _
      (M.dag.topoOrder_lt _ _ (M.dag.mem_parents.mp p.property)) k
  rw [← evalSteps_coordinate_eq_intervenedEval M (fun _ => none) u T
    (M.dag.topoOrder T + 1) (by omega) j]
  simp only [evalSteps, WithLp.ofLp_toLp, if_true, Option.getD_none]
  rw [nodeValue_eq_of_parentValues_eq M T _ _ u hp]

/-- [Extracting the treatment-parent values from the reconstructed joint
vector recovers the original parent vector exactly](goal). -/
-- @node: parentValues_treatmentParentJoint
lemma parentValues_treatmentParentJoint (M : EuclideanSCM kind dims) (T : Fin n)
    (x : ParentSpace M T) : parentValues M T (treatmentParentJoint M T x) = x := by
  apply WithLp.ofLp_injective
  funext ⟨i,j⟩
  simp [parentValues, treatmentParentJoint, i.property]

/-- Suppose [the treatment has one real coordinate](hyp:hT), [the latent blocks
are independent](hyp:hind), and [there is no hidden confounding](hyp:hnoconf).
For [a nonnegative, possibly infinite density p indexed by parent values and
treatment level](hyp:p), assume [p is a measurable version of the treatment's
conditional density given its observed parents, relative to the reference
probability P](hyp:hdensity) and [for almost every
observed parent vector, p is at least the nonnegative part of delta at every
treatment level in the closed interval from t1 to t2](hyp:hoverlap); then
[the joint observational law of the scalar treatment and its full
non-descendant vector dominates the product of P restricted to that interval
and the observational non-descendant law, scaled by the nonnegative part of
delta](goal). -/
-- @node: treatment_reference_nonDescendant_product_le
lemma treatment_reference_nonDescendant_product_le
    (M : CanonicalSCM kind dims dag G C) (T : Fin n)
    (hT : valueDim (kind T) = 1)
    (hind : LatentBlocksIndependent M.toEuclideanSCM) (hnoconf : NoHiddenConfounding G)
    (P : ProbabilityMeasure ℝ) (p : ParentSpace M.toEuclideanSCM T × ℝ → ℝ≥0∞)
    (delta t1 t2 : ℝ)
    (hdensity : TreatmentReferenceDensity M.toEuclideanSCM T (scalarOutcome T hT) P p)
    (hoverlap : ∀ᵐ x ∂((observationalLaw M.toEuclideanSCM).map
      (parentValues M.toEuclideanSCM T)),
      ∀ t ∈ Set.Icc t1 t2, ENNReal.ofReal delta ≤ p (x,t)) :
    ENNReal.ofReal delta •
      (((P : Measure ℝ).restrict (Set.Icc t1 t2)).prod
        ((observationalLaw M.toEuclideanSCM).map (nonDescendantProjection (dag := dag) T))) ≤
      (observationalLaw M.toEuclideanSCM).map (fun v =>
        (scalarOutcome T hT v, nonDescendantProjection (dag := dag) T v)) := by
  letI := M.latentLaw_probability
  let v := intervenedEval M.toEuclideanSCM (fun _ => none)
  let a := fun u => nonDescendantProjection (dag := dag) T (v u)
  let parent := parentValues M.toEuclideanSCM T
  let z : Exogenous kind dims → Exogenous kind dims := restrictLatentFamily (nodeLatentIndices (C := C) T)
  let F : ParentSpace M.toEuclideanSCM T × Exogenous kind dims → ℝ := fun w =>
    (nodeValue M.toEuclideanSCM T (treatmentParentJoint M.toEuclideanSCM T w.1) w.2).ofLp
      (Fin.cast hT.symm ⟨0, by decide⟩)
  have hv : Measurable v := by
    first | fun_prop | exact evalSteps_measurable M.toEuclideanSCM _ _
  have ha : Measurable a := by dsimp [a]; fun_prop
  have hp : Measurable parent := by
    first | fun_prop | skip
    exact scm_toLp_measurable.comp (measurable_pi_lambda _ fun c =>
      (measurable_pi_apply _).comp scm_ofLp_measurable)
  have hz : Measurable z := by dsimp [z]; fun_prop
  have hF : Measurable F := by fun_prop
  have heq (u : Exogenous kind dims) : F (parent (a u), z u) = scalarOutcome T hT (v u) := by
    have hpv : parentValues M.toEuclideanSCM T
        (treatmentParentJoint M.toEuclideanSCM T (parent (a u))) =
        parentValues M.toEuclideanSCM T (v u) := by
      rw [parentValues_treatmentParentJoint]
      exact parentValues_nonDescendantProjection M.toEuclideanSCM T (v u)
    dsimp only [F]
    rw [nodeValue_eq_of_parentValues_eq M.toEuclideanSCM T _ _ (z u) hpv]
    rw [← nodeValue_restrict_node_noise M T (v u) u]
    exact (observational_treatment_eq_nodeValue M.toEuclideanSCM T u _).symm
  have hparentlaw : M.latentLaw.map (parent ∘ a) =
      (observationalLaw M.toEuclideanSCM).map parent := by
    rw [show observationalLaw M.toEuclideanSCM = M.latentLaw.map v from rfl,
      Measure.map_map hp hv]
    congr 1
    funext u
    exact parentValues_nonDescendantProjection M.toEuclideanSCM T (v u)
  have hjointlaw : M.latentLaw.map (fun u => (parent (a u), F (parent (a u), z u))) =
      (observationalLaw M.toEuclideanSCM).map (fun w => (parent w, scalarOutcome T hT w)) := by
    rw [show observationalLaw M.toEuclideanSCM = M.latentLaw.map v from rfl,
      Measure.map_map (hp.prodMk (by fun_prop [scalarOutcome])) hv]
    congr 1
    funext u
    exact Prod.ext (parentValues_nonDescendantProjection M.toEuclideanSCM T (v u)) (heq u)
  have hden : ∀ᵐ x ∂M.latentLaw.map (parent ∘ a),
      (M.latentLaw.map (fun u => (parent (a u), F (parent (a u), z u)))).condKernel x =
        (P : Measure ℝ).withDensity (fun t => p (x,t)) := by
    simpa only [hparentlaw, hjointlaw] using hdensity.2.2.2
  have hlow : ∀ᵐ x ∂M.latentLaw.map (parent ∘ a),
      ∀ t ∈ Set.Icc t1 t2, ENNReal.ofReal delta ≤ p (x,t) := by
    rw [hparentlaw]
    exact hoverlap
  have hdom := independent_simulation_overlap_lift M.latentLaw a parent z F ha hp hz hF
    (nonDescendant_indep_treatment_noise M hnoconf hind T) (P : Measure ℝ)
    (Set.Icc t1 t2) measurableSet_Icc p delta hden hlow
  have hswap := Measure.map_mono hdom measurable_swap
  have hactualm : Measurable (fun u => (a u, F (parent (a u), z u))) :=
    ha.prodMk (hF.comp ((hp.comp ha).prodMk hz))
  rw [Measure.map_smul, Measure.prod_swap,
    Measure.map_map measurable_swap hactualm] at hswap
  have hAlaw : M.latentLaw.map a = (observationalLaw M.toEuclideanSCM).map
      (nonDescendantProjection (dag := dag) T) :=
    (Measure.map_map (nonDescendantProjection_measurable T) hv).symm
  rw [hAlaw] at hswap
  convert hswap using 1
  rw [show observationalLaw M.toEuclideanSCM = M.latentLaw.map v from rfl,
    Measure.map_map ((by fun_prop [scalarOutcome] : Measurable (scalarOutcome T hT)).prodMk
      (nonDescendantProjection_measurable T)) hv]
  congr 1
  funext u
  exact Prod.ext (heq u).symm rfl

end
end Papers.TbsNeuralCausalPi
