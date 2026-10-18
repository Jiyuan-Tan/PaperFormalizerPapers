module
public import Papers.TbsNeuralCausalPi.Setup.Assumptions.Estimation
public import Papers.TbsNeuralCausalPi.Helpers.WassersteinBounds
public import Papers.TbsNeuralCausalPi.Helpers.CategoricalCoupling
public import Mathlib.Probability.Independence.Integration
/-! # Descendant means and the backdoor regression bridge -/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

/-- For [a system of n nodes](hyp:n) with [the specified numerical or categorical node types](hyp:kind),
the [categorical comparison factor](goal) is the maximum of one and the supremum of
the node factors, where numerical nodes contribute zero and a categorical node with
k labels contributes half of k minus one. -/
def categoricalFactor (kind : Fin n → NodeKind) : ℝ := -- @realizes D(maximum of one and the categorical cardinality factors for dose-response comparison)
  max 1 (sSup (Set.range (fun i => match kind i with
    | .inl _ => (0:ℝ) | .inr k => (k-1 : ℕ)/2)))
/-- For [n nodes](hyp:n) with [the specified node types](hyp:kind) and
[nonnegative structural Lipschitz bound L](hyp:L), the [dose Lipschitz bound](goal)
is one plus L times the categorical comparison factor, raised to the power n. -/
def doseLip (kind : Fin n → NodeKind) (L : ℝ≥0) : ℝ := (L * categoricalFactor kind+1)^n
/-- For [n nodes](hyp:n) with [the specified node types](hyp:kind),
[nonnegative Lipschitz bound L](hyp:L), and [nonnegative numerical bound K](hyp:K),
the [dose comparison coefficient](goal) is computed by [taking the dose Lipschitz bound as Ly](step:1),
[setting B to K times one plus twice the total coordinate dimension times Ly](step:2),
and [returning four times Ly times B plus twice B times the maximum of Ly and one](step:3). -/
def doseCW (kind : Fin n → NodeKind) (L : ℝ≥0) (K : ℝ≥0) : ℝ := -- @realizes C_W(comparison coefficient computed from the dose Lipschitz constant and numerical bound)
  let Ly := doseLip kind L
  let B := (K : ℝ) * (1+2*(∑ i, valueDim (kind i))*Ly)
  4*Ly*B+2*B*max Ly 1

/-- For [n nodes](hyp:n) with [the specified node types](hyp:kind),
[treatment node T](hyp:T), and [real dose t](hyp:t), the [single-node intervention](goal)
assigns t to every coordinate of T and leaves every other node unassigned. -/
def singleIntervention (T : Fin n) (t : ℝ) : Intervention kind := -- @realizes T(one-node scalar treatment assignment)
  fun i => if i = T then some (WithLp.toLp 1 (fun _ => t)) else none
/-- For [n nodes](hyp:n) with [the specified node types](hyp:kind),
[treatment node T](hyp:T), and [real dose t](hyp:t), the [admissible intervention family](goal)
uses the single-node assignment at T when admissible and otherwise uses no intervention.

Overlap and absolute continuity ensure agreement almost everywhere in its consumers. -/
def singleLawIntervention (T : Fin n) (t : ℝ) : LawIntervention kind :=
  if ht : AdmissibleIntervention kind (singleIntervention T t) then
    ⟨singleIntervention T t, ht⟩ else noIntervention kind

/-- For [n nodes](hyp:n) with [the specified node types](hyp:kind),
[admissibility of a joint value vector](goal) means that assigning all nodes the
coordinates in [the vector v](hyp:v) is an admissible intervention. -/
def admissibleJoint (v : Joint kind) : Prop :=
  AdmissibleIntervention kind (fun i => some (WithLp.toLp 1 (fun j => v.ofLp ⟨i,j⟩)))
/-- For [n nodes](hyp:n) with [the specified node types](hyp:kind),
[outcome node Y](hyp:Y), [whose coordinate dimension is one](hyp:hY), and
[joint value vector v](hyp:v), the [scalar outcome](goal) is Y's sole coordinate. -/
def scalarOutcome (Y : Fin n) (hY : valueDim (kind Y) = 1) (v : Joint kind) : ℝ := -- @realizes Y(scalar outcome coordinate projection)
  v.ofLp ⟨Y, Fin.cast hY.symm ⟨0, Nat.zero_lt_succ 0⟩⟩
/-- For [n nodes](hyp:n) with [node types](hyp:kind) and [latent-block dimensions](hyp:dims)
indexed by [b blocks](hyp:b), [structural causal model M](hyp:M),
[treatment node T](hyp:T), and [outcome node Y](hyp:Y) [of dimension one](hyp:hY),
the [mean outcome at dose t](goal) integrates Y over the latent law after assigning
[dose t](hyp:t) to T. -/
def meanOutcome (M : EuclideanSCM kind dims) (T Y : Fin n)
    (hY : valueDim (kind Y) = 1) (t : ℝ) : ℝ :=
  ∫ u, scalarOutcome Y hY (intervenedEval M (singleIntervention T t) u) ∂M.latentLaw
/-- In [a system of n nodes](hyp:n) with [directed acyclic graph](hyp:dag),
the [non-descendant set](goal) of [treatment node T](hyp:T) contains precisely
the nodes other than T for which T is not an ancestor. -/
def nonDescendantNodes (T : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i ≠ T ∧ ¬ dag.isAncestor T i)
/-- For [n nodes](hyp:n) of [the specified types](hyp:kind), [b latent blocks](hyp:b)
with [the specified dimensions](hyp:dims), [directed graph](hyp:dag),
[bidirected graph](hyp:G), and [latent-block node sets](hyp:C), take
[canonical structural causal model M](hyp:M), [treatment T](hyp:T), and
[outcome Y](hyp:Y) [of dimension one](hyp:hY). The [descendant mean](goal)
integrates Y over the latent law after assigning [dose t](hyp:t) to T and
fixing T's non-descendants to [their coordinates in a](hyp:a). -/
def descendantMean (M : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hY : valueDim (kind Y) = 1) (a : Joint kind) (t : ℝ) : ℝ :=
  ∫ u, scalarOutcome Y hY (intervenedEval M.toEuclideanSCM
    (fun i => if i = T then some (WithLp.toLp 1 (fun _ => t)) else
      if i ∈ nonDescendantNodes (dag := dag) T then
        some (WithLp.toLp 1 (fun j => a.ofLp ⟨i,j⟩)) else none) u) ∂M.latentLaw

/-- For [n nodes](hyp:n) of [the specified types](hyp:kind) with
[directed graph](hyp:dag) and [treatment node T](hyp:T), the
[non-descendant projection](goal) retains the coordinates of [joint vector v](hyp:v)
at T's non-descendants and sets all remaining coordinates to zero. -/
def nonDescendantProjection (T : Fin n) (v : Joint kind) : Joint kind :=
  WithLp.toLp 1 (fun ⟨i,j⟩ => if i ∈ nonDescendantNodes (dag := dag) T then v.ofLp ⟨i,j⟩ else 0)

/-- Given [parameter-dependent assignment values for each node](hyp:v)
that [are measurable in the parameter at every node](hyp:hv),
[the structural evaluation after r steps, with the nodes in S assigned these
values, is jointly measurable in the parameter and latent inputs](goal). -/
-- @node: evalSteps_measurable_parametric_assignment
@[fun_prop] lemma evalSteps_measurable_parametric_assignment
    {X : Type*} [MeasurableSpace X] (M : EuclideanSCM kind dims)
    (S : Finset (Fin n)) (v : ∀ i, X → L1Vec (valueDim (kind i)))
    (hv : ∀ i, Measurable (v i)) (r : ℕ) :
    Measurable (fun z : X × Exogenous kind dims =>
      evalSteps M (fun i => if i ∈ S then some (v i z.1) else none) z.2 r) := by
  first | fun_prop | skip
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    simp only [evalSteps]
    apply scm_toLp_measurable.comp
    apply measurable_pi_lambda
    rintro ⟨i,j⟩
    by_cases hi : M.dag.topoOrder i = r
    · simp only [hi, if_true]
      by_cases hs : i ∈ S
      · simp only [hs, if_true, Option.getD_some]
        exact (measurable_pi_apply j).comp
          (scm_ofLp_measurable.comp ((hv i).comp measurable_fst))
      · simp only [hs, if_false, Option.getD_none]
        have hm : Measurable (fun z : X × Exogenous kind dims =>
            nodeValue M i
              (evalSteps M (fun i => if i ∈ S then some (v i z.1) else none) z.2 r) z.2) := by
          first | fun_prop | exact (nodeValue_measurable M i).comp (ih.prodMk measurable_snd)
        exact (measurable_pi_apply j).comp (scm_ofLp_measurable.comp hm)
    · simp only [hi, if_false]
      exact (measurable_pi_apply ⟨i,j⟩).comp (scm_ofLp_measurable.comp ih)

/-- If [the outcome node has dimension one](hyp:hY), then
[its mean under a single-node treatment intervention is a measurable function of the dose](goal). -/
-- @node: meanOutcome_measurable
@[fun_prop] lemma meanOutcome_measurable (M : EuclideanSCM kind dims)
    (T Y : Fin n) (hY : valueDim (kind Y) = 1) :
    Measurable (meanOutcome M T Y hY) := by
  first | fun_prop | skip
  letI := M.probability
  have hm : Measurable (fun z : ℝ × Exogenous kind dims =>
      intervenedEval M (singleIntervention T z.1) z.2) := by
    first | fun_prop | skip
    change Measurable (fun z : ℝ × Exogenous kind dims =>
      evalSteps M (fun i => if i = T then some (WithLp.toLp 1 (fun _ => z.1)) else none)
        z.2 (n*n+n))
    simpa only [Finset.mem_singleton] using
      evalSteps_measurable_parametric_assignment M {T}
        (fun (_ : Fin n) (t : ℝ) => WithLp.toLp 1 (fun _ => t)) (by intro i; fun_prop) (n*n+n)
  have hy : Measurable (fun z : ℝ × Exogenous kind dims =>
      scalarOutcome Y hY (intervenedEval M (singleIntervention T z.1) z.2)) := by
    first | fun_prop | skip
    exact (measurable_pi_apply _).comp (scm_ofLp_measurable.comp hm)
  exact hy.stronglyMeasurable.integral_prod_right'.measurable

/-- [The structural simulation that assigns the treatment dose and fixes its
non-descendants to given covariate values is jointly measurable in those
covariate values, the dose, and all latent inputs](goal), including off observational support. -/
-- @node: descendantEval_measurable
@[fun_prop] lemma descendantEval_measurable (M : CanonicalSCM kind dims dag G C)
    (T : Fin n) :
    Measurable (fun z : (Joint kind × ℝ) × Exogenous kind dims =>
      intervenedEval M.toEuclideanSCM
        (fun i => if i = T then some (WithLp.toLp 1 (fun _ => z.1.2)) else
          if i ∈ nonDescendantNodes (dag := dag) T then
            some (WithLp.toLp 1 (fun j => z.1.1.ofLp ⟨i,j⟩)) else none) z.2) := by
  first | fun_prop | skip
  let v : ∀ i, Joint kind × ℝ → L1Vec (valueDim (kind i)) :=
    fun i s => if i = T then WithLp.toLp 1 (fun _ => s.2) else
      WithLp.toLp 1 (fun j => s.1.ofLp ⟨i,j⟩)
  have hv : ∀ i, Measurable (v i) := by
    intro i
    first | fun_prop | skip
    dsimp [v]
    split_ifs <;> fun_prop
  have h := evalSteps_measurable_parametric_assignment M.toEuclideanSCM
    (insert T (nonDescendantNodes (dag := dag) T)) v hv (n*n+n)
  convert h using 1
  funext z
  congr 1
  funext i
  by_cases hi : i = T
  · simp [hi, v]
  · simp [hi, v]

/-- If [the outcome node has dimension one](hyp:hY), then
[the descendant mean is jointly measurable in the fixed joint value vector and treatment dose](goal). -/
-- @node: descendantMean_measurable
@[fun_prop] lemma descendantMean_measurable (M : CanonicalSCM kind dims dag G C)
    (T Y : Fin n) (hY : valueDim (kind Y) = 1) :
    Measurable (fun s : Joint kind × ℝ => descendantMean M T Y hY s.1 s.2) := by
  first | fun_prop | skip
  letI := M.latentLaw_probability
  have hm : Measurable (fun z : (Joint kind × ℝ) × Exogenous kind dims =>
      scalarOutcome Y hY (intervenedEval M.toEuclideanSCM
        (fun i => if i = T then some (WithLp.toLp 1 (fun _ => z.1.2)) else
          if i ∈ nonDescendantNodes (dag := dag) T then
            some (WithLp.toLp 1 (fun j => z.1.1.ofLp ⟨i,j⟩)) else none) z.2)) := by
    first | fun_prop | skip
    exact (measurable_pi_apply _).comp
      (scm_ofLp_measurable.comp (descendantEval_measurable M T))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- If [the outcome has dimension one](hyp:hY) and [the treatment has dimension one](hyp:hT),
then [the descendant mean evaluated at the observed non-descendants and treatment
is strongly measurable for the sigma-algebra generated by those observations](goal). -/
-- @node: descendantMean_regression_stronglyMeasurable
@[fun_prop] lemma descendantMean_regression_stronglyMeasurable
    (M : CanonicalSCM kind dims dag G C) (T Y : Fin n)
    (hY : valueDim (kind Y) = 1) (hT : valueDim (kind T) = 1) :
    StronglyMeasurable[MeasurableSpace.comap
      (fun v : Joint kind => (nonDescendantProjection (dag := dag) T v,
        scalarOutcome T hT v)) (borel _)]
      (fun v => descendantMean M T Y hY (nonDescendantProjection (dag := dag) T v)
        (scalarOutcome T hT v)) := by
  first | fun_prop | skip
  letI : BorelSpace (Joint kind) := ⟨rfl⟩
  have hb : borel (Joint kind × ℝ) = (inferInstance : MeasurableSpace (Joint kind × ℝ)) :=
    (BorelSpace.measurable_eq (α := Joint kind × ℝ)).symm
  rw [hb]
  exact ((descendantMean_measurable M T Y hY).comp
    (comap_measurable _)).stronglyMeasurable

/-- If [node i is categorical with k labels](hyp:hk) and
[its topological slot precedes step r](hyp:hr), then
[after r observational evaluation steps there is a label from zero through k minus one
such that every coordinate of node i equals that label plus one](goal). -/
-- @node: evalSteps_categorical_label
lemma evalSteps_categorical_label (M : EuclideanSCM kind dims)
    (u : Exogenous kind dims) (i : Fin n) (k : ℕ) (hk : kind i = .inr k)
    (r : ℕ) (hr : M.dag.topoOrder i < r) :
    ∃ label : Fin k, ∀ j,
      (evalSteps M (fun _ => none) u r).ofLp ⟨i,j⟩ = (label.val + 1 : ℕ) := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hi : M.dag.topoOrder i = r
    · have hlabel := observedValueEmbedding_categorical_label hk
        (M.f i (structuralInput M i (evalSteps M (fun _ => none) u r) u)
          (categoricalNoise i u))
      obtain ⟨label, hlabel⟩ := hlabel
      refine ⟨label, ?_⟩
      intro j
      simp only [evalSteps, WithLp.ofLp_toLp, hi, if_true, Option.getD_none]
      have heq : nodeValue M i (evalSteps M (fun _ => none) u r) u =
          observedValueEmbedding (kind i)
            (M.f i (structuralInput M i (evalSteps M (fun _ => none) u r) u)
              (categoricalNoise i u)) := (observedValueEmbedding_eq _ _).symm
      rw [heq]
      exact hlabel j
    · obtain ⟨label, hlabel⟩ := ih (by omega)
      refine ⟨label, ?_⟩
      intro j
      simpa only [evalSteps, WithLp.ofLp_toLp, hi, if_false] using hlabel j

/-- [Every node's topological number in the structural model is strictly less
than the evaluation horizon n squared plus n](goal). -/
-- @node: scm_topoOrder_lt_horizon
lemma scm_topoOrder_lt_horizon (M : EuclideanSCM kind dims) (i : Fin n) :
    M.dag.topoOrder i < n * n + n := by
  have hr : M.dag.ancestorRank i ≤ n := by
    simpa [Causalean.Graph.DAG.ancestorRank] using
      (Finset.card_le_univ (s := M.dag.ancClosure i))
  have he : (Fintype.equivFin (Fin n) i).val < n := by
    simpa using (Fintype.equivFin (Fin n) i).isLt
  simpa only [Causalean.Graph.DAG.topoOrder, Fintype.card_fin] using
    (add_lt_add_of_le_of_lt (Nat.mul_le_mul_right n hr) he)

/-- If [the dose is unrestricted when T is numerical and equals a valid label
plus one when T is categorical](hyp:ht), then
[assigning that dose to T alone is an admissible intervention](goal). -/
-- @node: singleIntervention_admissible_of_label
lemma singleIntervention_admissible_of_label (T : Fin n) (t : ℝ)
    (ht : match kind T with
      | .inl _ => True
      | .inr k => ∃ label : Fin k, t = (label.val + 1 : ℕ)) :
    AdmissibleIntervention kind (singleIntervention T t) := by
  intro i v hv
  by_cases hi : i = T
  · subst i
    simp only [singleIntervention, if_pos rfl, if_true, Option.some.injEq] at hv
    subst v
    cases hk : kind T with
    | inl d => trivial
    | inr k =>
      obtain ⟨label, hlabel⟩ := (show ∃ label : Fin k, t = (label.val + 1 : ℕ) from by
        simpa only [hk] using ht)
      exact ⟨label, fun _ => hlabel⟩
  · simp [singleIntervention, hi] at hv

/-- Given [a candidate density p depending on parent values and treatment](hyp:p)
that [represents the conditional treatment law relative to the reference law](hyp:hdensity),
[a strictly positive overlap level delta](hyp:hdelta), and
[a lower bound of delta on p throughout the closed intervention interval for almost every
observed parent vector](hyp:hoverlap), if [S is measurable](hyp:hS) and
[observational treatments belong to S almost surely](hyp:hobs), then
[reference treatments restricted to that interval belong to S almost surely](goal). -/
-- @node: treatment_reference_ae_mem_of_observational
lemma treatment_reference_ae_mem_of_observational (M : EuclideanSCM kind dims)
    (T : Fin n) (P : ProbabilityMeasure ℝ) (treatment : Joint kind → ℝ)
    (p : ParentSpace M T × ℝ → ℝ≥0∞) (delta t1 t2 : ℝ)
    (hdensity : TreatmentReferenceDensity M T treatment P p) (hdelta : 0 < delta)
    (hoverlap : ∀ᵐ x ∂((observationalLaw M).map (parentValues M T)),
      ∀ t ∈ Set.Icc t1 t2, ENNReal.ofReal delta ≤ p (x,t))
    {S : Set ℝ} (hS : MeasurableSet S)
    (hobs : ∀ᵐ v ∂observationalLaw M, treatment v ∈ S) :
    ∀ᵐ t ∂((P : Measure ℝ).restrict (Set.Icc t1 t2)), t ∈ S := by
  let obs := observationalLaw M
  letI : IsFiniteMeasure obs := observationalLaw_finite M
  let rho := obs.map (fun v => (parentValues M T v, treatment v))
  have htm : Measurable treatment := hdensity.2.1
  have hp : Measurable p := hdensity.2.2.1
  have hparent : Measurable (parentValues M T) := by
    first | fun_prop | skip
    unfold parentValues
    exact scm_toLp_measurable.comp (measurable_pi_lambda _ fun c =>
      (measurable_pi_apply _).comp scm_ofLp_measurable)
  have hjoint : Measurable (fun v => (parentValues M T v, treatment v)) := by
    fun_prop
  have hrho : ∀ᵐ z ∂rho, z.2 ∈ S :=
    (ae_map_iff hjoint.aemeasurable (measurable_snd hS)).2 hobs
  have hcond : ∀ᵐ x ∂obs.map (parentValues M T), ∀ᵐ t ∂rho.condKernel x, t ∈ S := by
    have h := Measure.ae_ae_of_ae_compProd
      (rho.disintegrate rho.condKernel ▸ hrho)
    simpa only [rho, Measure.fst_map_prodMk htm] using h
  letI := M.probability
  haveI : IsProbabilityMeasure obs := by
    dsimp [obs, observationalLaw, interventionalLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (obs.map (parentValues M T)) :=
    Measure.isProbabilityMeasure_map hparent.aemeasurable
  obtain ⟨x, hx, hdens, hlow⟩ :=
    (hcond.and (hdensity.2.2.2.and hoverlap)).exists
  have hdens' : rho.condKernel x = (P : Measure ℝ).withDensity (fun t => p (x,t)) := hdens
  rw [hdens'] at hx
  have hpt : Measurable (fun t => p (x,t)) := by fun_prop
  have href := (ae_withDensity_iff hpt).1 hx
  apply (ae_restrict_iff' measurableSet_Icc).2
  filter_upwards [href] with t ht hit
  exact ht (ne_of_gt ((ENNReal.ofReal_pos.mpr hdelta).trans_le (hlow t hit)))

/-- Suppose [T has dimension one](hyp:hT), [the model's variables are bounded by K](hyp:hbound),
and [the treatment function is T's scalar coordinate](hyp:htreatment). Given
[a candidate parent-dependent treatment density p](hyp:p) that
[represents the conditional treatment law relative to the reference law](hyp:hdensity),
[a positive delta](hyp:hdelta), and [a density lower bound of delta throughout
the closed intervention interval for almost every observed parent vector](hyp:hoverlap),
[almost every reference dose on that interval has absolute value at most K](goal). -/
-- @node: treatment_reference_ae_bounded
lemma treatment_reference_ae_bounded (M : EuclideanSCM kind dims)
    (T : Fin n) (hT : valueDim (kind T) = 1) (K : ℝ)
    (hbound : VariablesBoundedAt M K) (P : ProbabilityMeasure ℝ)
    (treatment : Joint kind → ℝ) (htreatment : treatment = scalarOutcome T hT)
    (p : ParentSpace M T × ℝ → ℝ≥0∞) (delta t1 t2 : ℝ)
    (hdensity : TreatmentReferenceDensity M T treatment P p) (hdelta : 0 < delta)
    (hoverlap : ∀ᵐ x ∂((observationalLaw M).map (parentValues M T)),
      ∀ t ∈ Set.Icc t1 t2, ENNReal.ofReal delta ≤ p (x,t)) :
    ∀ᵐ t ∂((P : Measure ℝ).restrict (Set.Icc t1 t2)), |t| ≤ K := by
  apply treatment_reference_ae_mem_of_observational M T P treatment p delta t1 t2
    hdensity hdelta hoverlap (S := {t | |t| ≤ K})
    (measurableSet_le (by fun_prop) measurable_const)
  have hm : Measurable treatment := hdensity.2.1
  change ∀ᵐ v ∂M.latentLaw.map (intervenedEval M (fun _ => none)),
    treatment v ∈ {t | |t| ≤ K}
  apply (ae_map_iff (by first | fun_prop | exact (evalSteps_measurable M _ _).aemeasurable)
    (hm (measurableSet_le (by fun_prop) measurable_const))).2
  filter_upwards [hbound.2] with u hu
  rw [htreatment]
  exact hu.1 T _

/-- Suppose [T has dimension one](hyp:hT) and [the treatment function is T's scalar coordinate](hyp:htreatment).
Given [a candidate parent-dependent treatment density p](hyp:p) that
[represents the conditional treatment law relative to the reference law](hyp:hdensity),
[a positive delta](hyp:hdelta), and [a density lower bound of delta throughout
the closed intervention interval for almost every observed parent vector](hyp:hoverlap),
[assigning a reference dose to T alone is admissible for almost every dose on that interval](goal). -/
-- @node: treatment_intervention_ae_admissible
lemma treatment_intervention_ae_admissible (M : EuclideanSCM kind dims)
    (T : Fin n) (hT : valueDim (kind T) = 1) (P : ProbabilityMeasure ℝ)
    (treatment : Joint kind → ℝ) (htreatment : treatment = scalarOutcome T hT)
    (p : ParentSpace M T × ℝ → ℝ≥0∞) (delta t1 t2 : ℝ)
    (hdensity : TreatmentReferenceDensity M T treatment P p) (hdelta : 0 < delta)
    (hoverlap : ∀ᵐ x ∂((observationalLaw M).map (parentValues M T)),
      ∀ t ∈ Set.Icc t1 t2, ENNReal.ofReal delta ≤ p (x,t)) :
    ∀ᵐ t ∂((P : Measure ℝ).restrict (Set.Icc t1 t2)),
      AdmissibleIntervention kind (singleIntervention T t) := by
  cases hk : kind T with
  | inl d =>
    exact Filter.Eventually.of_forall fun t =>
      singleIntervention_admissible_of_label T t (by simp [hk])
  | inr k =>
    let S : Set ℝ := {t | ∃ label : Fin k, t = (label.val + 1 : ℕ)}
    have hS : MeasurableSet S := by
      convert (Set.finite_range (fun label : Fin k => ((label.val + 1 : ℕ) : ℝ))).measurableSet using 1
      ext t
      simp only [S, Set.mem_setOf_eq, Set.mem_range, eq_comm]
    let obs := observationalLaw M
    have htm : Measurable treatment := hdensity.2.1
    have heval : ∀ u, treatment (intervenedEval M (fun _ => none) u) ∈ S := by
      intro u
      obtain ⟨label, hl⟩ := evalSteps_categorical_label M u T k hk
        (n*n+n) (scm_topoOrder_lt_horizon M T)
      refine ⟨label, ?_⟩
      rw [htreatment]
      exact hl _
    have hobs : ∀ᵐ v ∂obs, treatment v ∈ S := by
      change ∀ᵐ v ∂M.latentLaw.map (intervenedEval M (fun _ => none)), treatment v ∈ S
      apply (ae_map_iff (by
        first | fun_prop | exact (evalSteps_measurable M _ _).aemeasurable) (htm hS)).2
      exact Filter.Eventually.of_forall heval
    have href := treatment_reference_ae_mem_of_observational M T P treatment p
      delta t1 t2 hdensity hdelta hoverlap hS hobs
    filter_upwards [href] with t ht
    apply singleIntervention_admissible_of_label T t
    simpa only [hk] using (show ∃ label : Fin k, t = (label.val + 1 : ℕ) from ht)

/-- If [the bidirected graph has no hidden confounding](hyp:hnoconf) and
[i and k are distinct nodes](hyp:hik), then
[the sets of canonical latent blocks incident to i and k are disjoint](goal). -/
-- @node: canonicalIncidence_disjoint_of_noHiddenConfounding
lemma canonicalIncidence_disjoint_of_noHiddenConfounding
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    {i k : Fin n} (hik : i ≠ k) :
    Disjoint (canonicalIncidence C i) (canonicalIncidence C k) := by
  rw [Finset.disjoint_left]
  intro j hji hjk
  simp only [canonicalIncidence, Finset.mem_filter, Finset.mem_univ, true_and] at hji hjk
  exact hnoconf i k ((M.component j).maximalClique.1 hji hjk hik)

/-- If [there is no hidden confounding](hyp:hnoconf),
[latent block j is incident to node i](hyp:hji), and
[that same block is incident to node k](hyp:hjk), then [i and k are the same node](goal). -/
-- @node: canonicalIncidence_node_unique
lemma canonicalIncidence_node_unique
    (M : CanonicalSCM kind dims dag G C) (hnoconf : NoHiddenConfounding G)
    {j : Fin b} {i k : Fin n} (hji : j ∈ canonicalIncidence C i)
    (hjk : j ∈ canonicalIncidence C k) : i = k := by
  by_contra hik
  exact Finset.disjoint_left.mp
    (canonicalIncidence_disjoint_of_noHiddenConfounding M hnoconf hik) hji hjk

/-- If [x is almost everywhere measurable under the finite measure](hyp:hx),
[z is almost everywhere measurable under that measure](hyp:hz),
[x and z are independent](hyp:hind), and [F is integrable under the product of their marginal laws](hyp:hF),
then [the integral of F evaluated at x and z equals the iterated integral of F,
first over z's marginal law and then over x's marginal law](goal). -/
-- @node: integral_indepFun_eq_iterated
lemma integral_indepFun_eq_iterated
    {Omega X Z : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace Z] (mu : Measure Omega) [IsFiniteMeasure mu]
    (x : Omega → X) (z : Omega → Z) (F : X × Z → ℝ)
    (hx : AEMeasurable x mu) (hz : AEMeasurable z mu)
    (hind : ProbabilityTheory.IndepFun x z mu)
    (hF : Integrable F ((mu.map x).prod (mu.map z))) :
    ∫ omega, F (x omega, z omega) ∂mu =
      ∫ xv, ∫ zv, F (xv, zv) ∂(mu.map z) ∂(mu.map x) := by
  have hpair := hind.map_prod_eq_prod_map_map hx hz
  have hFm : AEStronglyMeasurable F (mu.map fun omega => (x omega, z omega)) := by
    rw [hpair]
    exact hF.aestronglyMeasurable
  calc
    ∫ omega, F (x omega, z omega) ∂mu =
        ∫ xz, F xz ∂(mu.map fun omega => (x omega, z omega)) :=
      (integral_map (hx.prodMk hz) hFm).symm
    _ = ∫ xz, F xz ∂((mu.map x).prod (mu.map z)) := by rw [hpair]
    _ = ∫ xv, ∫ zv, F (xv, zv) ∂(mu.map z) ∂(mu.map x) :=
      integral_prod F hF




end
end Papers.TbsNeuralCausalPi
