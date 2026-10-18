module
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseRegression
public import Papers.TbsNeuralCausalPi.Helpers.InterventionDomains
/-! # Finite moments under fixed interventions

Bounded non-Gumbel inputs and structural Lipschitzness give bounded coordinates
at each finite evaluation step. Gumbel inputs enter only finite label outputs.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false
set_option linter.unusedVariables false
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

-- @node: nodeValue_continuous_coordinate
/-- If [the node is continuous with the specified dimension](hyp:hi), [each
coordinate of its realized value equals the corresponding coordinate of its
continuous structural map evaluated at the assembled structural input](goal). -/
lemma nodeValue_continuous_coordinate (M : EuclideanSCM kind dims)
    (i : Fin n) (d : ℕ) (hi : kind i = .inl d) (v : Joint kind)
    (u : Exogenous kind dims) (j : Fin (valueDim (kind i))) :
    (nodeValue M i v u).ofLp j =
      (M.continuousMap i (structuralInput M i v u)).ofLp
        (Fin.cast (by simp [hi, valueDim, outputDim]) j) := by
  have he (κ : NodeKind) (F : L1Vec (noiseDim κ) → ObservedValue κ)
      (hκ : κ = .inl d) (g : L1Vec (noiseDim κ)) (j : Fin (valueDim κ)) :
      (show L1Vec (valueDim κ) from match (generalizing := false) h : κ with
        | .inl d => cast (congrArg ObservedValue h) (F g)
        | .inr k => WithLp.toLp 1 (fun _ =>
            ((cast (congrArg ObservedValue h) (F g)).val + 1 : ℕ))).ofLp j =
      (show L1Vec (outputDim κ) from match (generalizing := false) h : κ with
        | .inl d => WithLp.toLp 1 (fun j => (cast (congrArg ObservedValue h) (F 0)).ofLp j)
        | .inr _ => 0).ofLp (Fin.cast (by simp [hκ, valueDim, outputDim]) j) := by
    subst κ
    have hg : g = 0 := by
      apply WithLp.ofLp_injective
      funext k
      exact Fin.elim0 k
    subst g
    rfl
  exact he (kind i) (M.f i (structuralInput M i v u)) hi (categoricalNoise i u) j

-- @node: continuousMap_bounded_on_coordinate_box
/-- For [a nonnegative Lipschitz constant](hyp:L), suppose [the continuous
mechanisms obey that Lipschitz bound on their admissible domains](hyp:hcont) and
[the chosen node is continuous with the specified dimension](hyp:hi). Then [its
continuous structural map has a uniform finite norm bound over all admissible
inputs whose coordinates are bounded in absolute value by the given radius](goal). -/
lemma continuousMap_bounded_on_coordinate_box (M : EuclideanSCM kind dims)
    (L : ℝ≥0) (hcont : ContinuousMechanismsLipschitz M L)
    (i : Fin n) (d : ℕ) (hi : kind i = .inl d) (R : ℝ) :
    ∃ B : ℝ, ∀ x ∈ M.domain i none,
      (∀ j, |x.ofLp j| ≤ R) → ‖M.continuousMap i x‖ ≤ B := by
  let x0 : StructuralInput kind dims M.dag M.incidence i := WithLp.toLp 1 (fun _ => 1)
  have hx0 : x0 ∈ M.domain i none := by
    refine ⟨?_, Set.mem_univ _⟩
    intro p k hk
    exact ⟨⟨0, M.categoricalPositive p.val k hk⟩, fun _ => by simp [x0]⟩
  refine ⟨‖M.continuousMap i x0‖ + (L : ℝ) *
    (∑ _j : Sum (Σ p : {p // p ∈ M.dag.parents i}, Fin (valueDim (kind p.val)))
      (Σ k : {k // k ∈ M.incidence i}, Fin (dims k.val)), (R + 1)), ?_⟩
  intro x hx hR
  have hd : dist x x0 ≤ ∑ _j : Sum (Σ p : {p // p ∈ M.dag.parents i}, Fin (valueDim (kind p.val)))
      (Σ k : {k // k ∈ M.incidence i}, Fin (dims k.val)), (R + 1) := by
    rw [PiLp.dist_eq_of_L1]
    apply Finset.sum_le_sum
    intro j _
    change |x.ofLp j - 1| ≤ R + 1
    calc
      |x.ofLp j - 1| ≤ |x.ofLp j| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ R + 1 := by simpa using add_le_add_right (hR j) 1
  calc
    ‖M.continuousMap i x‖ ≤ ‖M.continuousMap i x0‖ +
        dist (M.continuousMap i x) (M.continuousMap i x0) := by
      simpa [dist_eq_norm, norm_sub_rev] using norm_le_norm_add_norm_sub (M.continuousMap i x0) (M.continuousMap i x)
    _ ≤ ‖M.continuousMap i x0‖ + (L : ℝ) * dist x x0 :=
      add_le_add_right ((hcont i d hi).dist_le_mul x hx x0 hx0) _
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hd L.coe_nonneg) _

-- @node: nodeValue_bounded_on_coordinate_boxes
/-- For [a nonnegative Lipschitz constant](hyp:L), if [the continuous mechanisms
obey that Lipschitz bound on their admissible domains](hyp:hcont), [there is a
nonnegative uniform bound on every output coordinate of the chosen node whenever
its structural input is admissible, all joint-value coordinates satisfy the
given history bound, and all non-Gumbel block coordinates satisfy the given
noise bound](goal). -/
lemma nodeValue_bounded_on_coordinate_boxes (M : EuclideanSCM kind dims)
    (L : ℝ≥0) (hcont : ContinuousMechanismsLipschitz M L)
    (i : Fin n) (R K : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v u,
      structuralInput M i v u ∈ M.domain i none →
      (∀ i j, |v.ofLp ⟨i,j⟩| ≤ R) →
      (∀ k j, |(blockProjection k u).ofLp j| ≤ K) →
      ∀ j, |(nodeValue M i v u).ofLp j| ≤ B := by
  have hcases : (∃ d, kind i = .inl d) ∨ (∃ k, kind i = .inr k) := by
    cases kind i with
    | inl d => exact Or.inl ⟨d, rfl⟩
    | inr k => exact Or.inr ⟨k, rfl⟩
  rcases hcases with ⟨d, hi⟩ | ⟨k, hi⟩
  · obtain ⟨B, hB⟩ := continuousMap_bounded_on_coordinate_box M L hcont i d hi (max R K)
    refine ⟨max 0 B, le_max_left _ _, ?_⟩
    intro v u hx hv hu j
    rw [nodeValue_continuous_coordinate M i d hi]
    rw [← Real.norm_eq_abs]
    apply (PiLp.norm_apply_le _ _).trans
    apply (hB _ hx ?_).trans (le_max_right _ _)
    rintro (⟨p,j⟩ | ⟨k,j⟩)
    · exact (hv p.val j).trans (le_max_left _ _)
    · exact (hu k.val j).trans (le_max_right _ _)
  · refine ⟨k, Nat.cast_nonneg k, ?_⟩
    intro v u hx hv hu j
    obtain ⟨label, hlabel⟩ := observedValueEmbedding_categorical_label hi
      (M.f i (structuralInput M i v u) (categoricalNoise i u))
    have hn : nodeValue M i v u = observedValueEmbedding (kind i)
        (M.f i (structuralInput M i v u) (categoricalNoise i u)) :=
      (observedValueEmbedding_eq _ _).symm
    rw [hn, hlabel j, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.succ_le_of_lt label.isLt)

-- @node: evalSteps_bounded_of_nonGumbel_bounded
/-- For [a nonnegative Lipschitz constant](hyp:L), suppose [the continuous
mechanisms obey that Lipschitz bound on their admissible domains](hyp:hcont) and
[the fixed intervention is admissible](hyp:ht). Then [there is a nonnegative
uniform bound on all joint coordinates after the specified number of evaluation
steps for every exogenous input whose non-Gumbel block coordinates satisfy the
given bound](goal). -/
lemma evalSteps_bounded_of_nonGumbel_bounded (M : EuclideanSCM kind dims)
    (L : ℝ≥0) (hcont : ContinuousMechanismsLipschitz M L)
    (t : Intervention kind) (ht : AdmissibleIntervention kind t) (K : ℝ) (r : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ u : Exogenous kind dims,
      (∀ k j, |(blockProjection k u).ofLp j| ≤ K) →
      ∀ i j, |(evalSteps M t u r).ofLp ⟨i,j⟩| ≤ R := by
  induction r with
  | zero => exact ⟨0, le_rfl, by intros; simp [evalSteps]⟩
  | succ r ih =>
    obtain ⟨R, hR, hv⟩ := ih
    choose B hB hnode using fun i => nodeValue_bounded_on_coordinate_boxes M L hcont i R K
    let Q := R + ∑ i, B i + ∑ i, ‖(t i).getD 0‖
    have hsumB : 0 ≤ ∑ i, B i := Finset.sum_nonneg (fun i _ => hB i)
    have hsumt : 0 ≤ ∑ i, ‖(t i).getD 0‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    have hRQ : R ≤ Q := by dsimp [Q]; linarith
    have hBQ (i : Fin n) : B i ≤ Q := by
      have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hB j) (Finset.mem_univ i)
      dsimp [Q]
      linarith
    have htQ (i : Fin n) : ‖(t i).getD 0‖ ≤ Q := by
      have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => norm_nonneg ((t j).getD 0))
        (Finset.mem_univ i)
      dsimp [Q]
      linarith
    refine ⟨Q, hR.trans hRQ, ?_⟩
    intro u hu i j
    simp only [evalSteps, WithLp.ofLp_toLp]
    by_cases hi : M.dag.topoOrder i = r
    · simp only [hi, if_true]
      cases he : t i with
      | none =>
        simp only [Option.getD_none]
        exact (hnode i _ u (evalSteps_structuralInput_mem_domain M t ht u i r hi)
          (hv u hu) hu j).trans (hBQ i)
      | some v =>
        simp only [Option.getD_some]
        have htv : ‖v‖ ≤ Q := by simpa [he] using htQ i
        exact (PiLp.norm_apply_le v j).trans htv
    · simp only [hi, if_false]
      exact (hv u hu i j).trans hRQ

-- @node: interventional_scalarOutcome_integrable
/-- For [a nonnegative Lipschitz constant](hyp:L), suppose [the continuous
mechanisms obey that Lipschitz bound on their admissible domains](hyp:hcont),
[observational coordinates and non-Gumbel block coordinates are almost surely
bounded by the given positive constant](hyp:hbound), [the intervention is
admissible](hyp:ht), and [the outcome node has one coordinate](hyp:hY). Then [the
outcome under that intervention is integrable with respect to the latent law](goal). -/
lemma interventional_scalarOutcome_integrable (M : EuclideanSCM kind dims)
    (L : ℝ≥0) (hcont : ContinuousMechanismsLipschitz M L)
    (K : ℝ) (hbound : VariablesBoundedAt M K)
    (t : Intervention kind) (ht : AdmissibleIntervention kind t)
    (Y : Fin n) (hY : valueDim (kind Y) = 1) :
    Integrable (fun u => scalarOutcome Y hY (intervenedEval M t u)) M.latentLaw := by
  let := M.probability
  obtain ⟨R, hR, hv⟩ := evalSteps_bounded_of_nonGumbel_bounded M L hcont t ht K (n*n+n)
  have hm : Measurable (fun u => scalarOutcome Y hY (intervenedEval M t u)) := by
    first
    | fun_prop
    | exact (measurable_pi_apply _).comp (scm_ofLp_measurable.comp (evalSteps_measurable M t _))
  apply Integrable.of_bound hm.aestronglyMeasurable R
  filter_upwards [hbound.2] with u hu
  exact hv u hu.2 Y _

-- @node: descendantEval_scalarOutcome_integrable
/-- For [a nonnegative Lipschitz constant](hyp:L), suppose [the canonical model's
continuous mechanisms obey that Lipschitz bound on their admissible domains](hyp:hcont),
[observational coordinates and non-Gumbel block coordinates are almost surely
bounded by the given positive constant](hyp:hbound), [the outcome node has one
coordinate](hyp:hY), [the fixed joint assignment is admissible](hyp:ha), and
[assigning the specified dose to the treatment node is admissible](hyp:ht). Then
[the scalar outcome is integrable under the latent law when the treatment is set
to that dose and its other non-descendants are fixed at the joint assignment](goal). -/
lemma descendantEval_scalarOutcome_integrable
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)} (M : CanonicalSCM kind dims dag G C)
    (L : ℝ≥0) (hcont : ContinuousMechanismsLipschitz M.toEuclideanSCM L)
    (K : ℝ) (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (T Y : Fin n) (hY : valueDim (kind Y) = 1)
    (a : Joint kind) (ha : admissibleJoint a)
    (t : ℝ) (ht : AdmissibleIntervention kind (singleIntervention T t)) :
    Integrable (fun u => scalarOutcome Y hY (intervenedEval M.toEuclideanSCM
      (fun i => if i = T then some (WithLp.toLp 1 (fun _ => t)) else
        if i ∈ nonDescendantNodes (dag := dag) T then
          some (WithLp.toLp 1 (fun j => a.ofLp ⟨i,j⟩)) else none) u)) M.latentLaw := by
  apply interventional_scalarOutcome_integrable M.toEuclideanSCM L hcont K hbound _ _ Y hY
  intro i v hv
  by_cases hi : i = T
  · exact ht i v (by simpa [singleIntervention, hi] using hv)
  · by_cases hn : i ∈ nonDescendantNodes (dag := dag) T
    · exact ha i v (by simpa [hi, hn] using hv)
    · simp [hi, hn] at hv

end
end Papers.TbsNeuralCausalPi
