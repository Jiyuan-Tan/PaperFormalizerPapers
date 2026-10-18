module
public import Papers.TbsNeuralCausalPi.Helpers.DoseResponseNonDescendant
public import Papers.TbsNeuralCausalPi.Helpers.InterventionalMoments
/-! # Complete observations with categorical labels fixed

Fixing every categorical node removes every intrinsic Gumbel input. The
remaining complete observation is a Lipschitz function of the joint latent
vector. Conditioning on a label stratum therefore requires no independence
between the coordinates of its conditional latent law.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

-- @node: jointNonGumbel
/-- From [an exogenous noise vector](hyp:u) for [the node types](hyp:kind) and
[latent block dimensions](hyp:dims), extract [the joint latent vector with all
intrinsic Gumbel coordinates discarded](goal). -/
def jointNonGumbel (u : Exogenous kind dims) : Latent dims :=
  WithLp.toLp 1 (fun c => u.ofLp (.inl c))

-- @node: nonGumbelLift
/-- Embed [a joint latent vector](hyp:z), with [block dimensions](hyp:dims), into
[the exogenous noise space for the given node types](hyp:kind) by defining
[the full noise vector whose latent coordinates are unchanged and whose intrinsic
noise coordinates are zero](goal). -/
def nonGumbelLift (z : Latent dims) : Exogenous kind dims :=
  WithLp.toLp 1 (Sum.elim z.ofLp (fun _ => 0))

-- @node: jointNonGumbel_measurable
/-- [Extracting the joint latent vector from the full exogenous noise is a
measurable map](goal). -/
@[fun_prop] lemma jointNonGumbel_measurable :
    Measurable (jointNonGumbel : Exogenous kind dims → Latent dims) := by
  fun_prop [jointNonGumbel]

-- @node: nonGumbelLift_measurable
/-- [Embedding the joint latent vector into the full exogenous noise by setting
all intrinsic noise coordinates to zero is measurable](goal). -/
@[fun_prop] lemma nonGumbelLift_measurable :
    Measurable (nonGumbelLift : Latent dims → Exogenous kind dims) := by
  apply scm_toLp_measurable.comp
  apply measurable_pi_lambda
  intro c
  cases c <;> dsimp only [Sum.elim] <;> fun_prop

-- @node: evalSteps_fixed_labels_eq_nonGumbelLift
/-- For [a structural causal model](hyp:M), [an intervention](hyp:t) that
[assigns every categorical node](hyp:hcover), [an exogenous noise vector](hyp:u),
and [any number of evaluation steps](hyp:r), [replacing all intrinsic noise by
zero while retaining the joint latent vector leaves the evaluated values
unchanged](goal).

Continuous nodes have zero-dimensional intrinsic noise by construction. -/
lemma evalSteps_fixed_labels_eq_nonGumbelLift (M : EuclideanSCM kind dims)
    (t : Intervention kind)
    (hcover : ∀ i k, kind i = .inr k → t i ≠ none)
    (u : Exogenous kind dims) (r : ℕ) :
    evalSteps M t u r = evalSteps M t (nonGumbelLift (jointNonGumbel u)) r := by
  apply evalSteps_eq_of_unassigned_noise_eq
  · intro i hi k hk j
    rfl
  · intro i hi
    have hc : ∃ d, kind i = .inl d := by
      cases he : kind i with
      | inl d => exact ⟨d, rfl⟩
      | inr k => exact False.elim (hcover i k he hi)
    obtain ⟨d, hd⟩ := hc
    have : Subsingleton (L1Vec (noiseDim (kind i))) := by
      rw [hd]
      change Subsingleton (L1Vec 0)
      infer_instance
    exact Subsingleton.elim _ _

-- @node: fixedLabelObservation
/-- For [a structural causal model](hyp:M), [an intervention](hyp:t), and
[a joint latent vector](hyp:z), define [the complete observation obtained by
evaluating the intervened model with that latent vector and zero intrinsic
noise](goal). -/
def fixedLabelObservation (M : EuclideanSCM kind dims) (t : Intervention kind)
    (z : Latent dims) : Joint kind := intervenedEval M t (nonGumbelLift z)

-- @node: fixedLabelObservation_measurable
/-- For [a structural causal model](hyp:M) and [an intervention](hyp:t),
[the complete observation with zero intrinsic noise is a measurable function
of the joint latent vector](goal). -/
@[fun_prop] lemma fixedLabelObservation_measurable (M : EuclideanSCM kind dims)
    (t : Intervention kind) : Measurable (fixedLabelObservation M t) := by
  fun_prop [fixedLabelObservation, intervenedEval]

-- @node: fixedLabelObservation_eq_factual
/-- For [a structural causal model](hyp:M), [an intervention](hyp:t) that
[assigns every categorical node](hyp:hcover), and [an exogenous noise
vector](hyp:u), if [every assigned coordinate equals its factual observed
value](hyp:hmatch), then [the intervened observation computed from the joint
latent vector with zero intrinsic noise equals the complete factual
observation](goal). -/
lemma fixedLabelObservation_eq_factual (M : EuclideanSCM kind dims)
    (t : Intervention kind) (hcover : ∀ i k, kind i = .inr k → t i ≠ none)
    (u : Exogenous kind dims)
    (hmatch : ∀ i v, t i = some v → ∀ j,
      v.ofLp j = (intervenedEval M (fun _ => none) u).ofLp ⟨i, j⟩) :
    fixedLabelObservation M t (jointNonGumbel u) =
      intervenedEval M (fun _ => none) u := by
  exact (evalSteps_fixed_labels_eq_nonGumbelLift M t hcover u (n*n+n)).symm.trans
    (evalSteps_eq_of_factual_assignments M (fun _ => none) t u (fun i => by
      cases ht : t i with
      | none => exact Or.inl rfl
      | some v =>
        apply Or.inr
        congr 1
        exact PiLp.ext (hmatch i v ht)) (n*n+n))

-- @node: structuralInput_dist_nonGumbelLift_le
/-- For [a structural causal model](hyp:M), [a node](hyp:i), [two complete
value vectors](hyp:v,w), and [two joint latent vectors](hyp:z,z'), [the distance
between the node's structural inputs with zero intrinsic noise is at most its
input dimension times the sum of the distances between the value vectors and
between the latent vectors](goal). -/
lemma structuralInput_dist_nonGumbelLift_le (M : EuclideanSCM kind dims)
    (i : Fin n) (v w : Joint kind) (z z' : Latent dims) :
    dist (structuralInput M i v (nonGumbelLift z))
      (structuralInput M i w (nonGumbelLift z')) ≤
        (structuralInputSize M i : ℝ) * (dist v w + dist z z') := by
  rw [PiLp.dist_eq_of_L1]
  calc
    _ ≤ ∑ _c : Sum (Σ p : {p // p ∈ M.dag.parents i}, Fin (valueDim (kind p)))
        (Σ j : {j // j ∈ M.incidence i}, Fin (dims j)),
        (dist v w + dist z z') := by
      apply Finset.sum_le_sum
      rintro (⟨p,j⟩ | ⟨a,j⟩) _
      · exact (PiLp.dist_apply_le v w ⟨p.val,j⟩).trans
          (le_add_of_nonneg_right dist_nonneg)
      · exact (PiLp.dist_apply_le z z' ⟨a.val,j⟩).trans
          (le_add_of_nonneg_left dist_nonneg)
    _ = _ := by simp [structuralInputSize, Fintype.card_sum, Fintype.card_sigma]; ring

-- @node: fixedLabelLipschitzBudget
/-- For [a structural causal model](hyp:M) and [a nonnegative mechanism
Lipschitz bound](hyp:L), define [a sequence of Lipschitz budgets for evaluation
with fixed categorical assignments](goal): [the initial budget is zero](step:1),
and [each subsequent budget is the total observation dimension times the sum
of the previous budget and the mechanism bound times the total structural
input dimension times one plus the previous budget](step:2). -/
def fixedLabelLipschitzBudget (M : EuclideanSCM kind dims) (L : ℝ≥0) : ℕ → ℝ≥0
  | 0 => 0
  | r + 1 => Fintype.card (Σ i, Fin (valueDim (kind i))) *
      (fixedLabelLipschitzBudget M L r +
        L * (∑ i, (structuralInputSize M i : ℝ≥0)) *
          (fixedLabelLipschitzBudget M L r + 1))

-- @node: evalSteps_fixed_labels_dist_le
/-- For [a structural causal model](hyp:M) and [a nonnegative bound](hyp:L)
such that [all continuous mechanisms are Lipschitz with that bound](hyp:hL),
consider [an admissible intervention](hyp:t) that [assigns every categorical
node](hyp:hcover), [a number of evaluation steps](hyp:r), and [two joint latent
vectors](hyp:z,z'). Then [the distance between their evaluated value vectors
with zero intrinsic noise is at most the recursive budget at that step times
the distance between the latent vectors](goal). -/
lemma evalSteps_fixed_labels_dist_le (M : EuclideanSCM kind dims)
    (L : ℝ≥0) (hL : ContinuousMechanismsLipschitz M L)
    (t : LawIntervention kind)
    (hcover : ∀ i k, kind i = .inr k → t.val i ≠ none)
    (r : ℕ) (z z' : Latent dims) :
    dist (evalSteps M t.val (nonGumbelLift z) r)
      (evalSteps M t.val (nonGumbelLift z') r) ≤
        (fixedLabelLipschitzBudget M L r : ℝ) * dist z z' := by
  induction r with
  | zero => simp [evalSteps, fixedLabelLipschitzBudget]
  | succ r ih =>
    let S : ℝ≥0 := ∑ i, (structuralInputSize M i : ℝ≥0)
    let A := fixedLabelLipschitzBudget M L r
    have hsize (i : Fin n) : (structuralInputSize M i : ℝ) ≤ S := by
      change ((structuralInputSize M i : ℝ≥0) : ℝ) ≤ (S : ℝ)
      apply NNReal.coe_le_coe.mpr
      exact (Finset.single_le_sum (f := fun i => (structuralInputSize M i : ℝ≥0))
        (fun _ _ => zero_le)
        (Finset.mem_univ i) : (structuralInputSize M i : ℝ≥0) ≤ S)
    have hinput (i : Fin n) :
        dist (structuralInput M i (evalSteps M t.val (nonGumbelLift z) r) (nonGumbelLift z))
          (structuralInput M i (evalSteps M t.val (nonGumbelLift z') r) (nonGumbelLift z')) ≤
            (S : ℝ) * ((A : ℝ) + 1) * dist z z' := by
      apply (structuralInput_dist_nonGumbelLift_le M i _ _ z z').trans
      calc
        _ ≤ (S : ℝ) * ((A : ℝ) * dist z z' + dist z z') :=
          mul_le_mul (hsize i) (add_le_add ih le_rfl) (by positivity) S.coe_nonneg
        _ = _ := by ring
    have hcoord (i : Fin n) (j : Fin (valueDim (kind i))) :
        dist ((evalSteps M t.val (nonGumbelLift z) (r+1)).ofLp ⟨i,j⟩)
          ((evalSteps M t.val (nonGumbelLift z') (r+1)).ofLp ⟨i,j⟩) ≤
            ((A : ℝ) + (L : ℝ) * S * ((A : ℝ) + 1)) * dist z z' := by
      by_cases hi : M.dag.topoOrder i = r
      · simp only [evalSteps, WithLp.ofLp_toLp, hi, if_true]
        cases ht : t.val i with
        | some v => simp only [Option.getD_some, dist_self]; positivity
        | none =>
          simp only [Option.getD_none]
          have hc : ∃ d, kind i = .inl d := by
            cases he : kind i with
            | inl d => exact ⟨d, rfl⟩
            | inr k => exact False.elim (hcover i k he ht)
          obtain ⟨d, hd⟩ := hc
          simp only [nodeValue_continuous_coordinate M i d hd]
          apply (PiLp.dist_apply_le _ _ _).trans
          apply ((hL i d hd).dist_le_mul _
            (evalSteps_structuralInput_mem_domain M t.val t.property _ i r hi) _
            (evalSteps_structuralInput_mem_domain M t.val t.property _ i r hi)).trans
          calc
            _ ≤ (L : ℝ) * ((S : ℝ) * ((A : ℝ) + 1) * dist z z') :=
              mul_le_mul_of_nonneg_left (hinput i) L.coe_nonneg
            _ ≤ _ := by nlinarith [mul_nonneg A.coe_nonneg (dist_nonneg (x := z) (y := z'))]
      · simp only [evalSteps, WithLp.ofLp_toLp, hi, if_false]
        apply ((PiLp.dist_apply_le _ _ ⟨i,j⟩).trans ih).trans
        have hn : 0 ≤ (L : ℝ) * S * ((A : ℝ) + 1) * dist z z' := by positivity
        dsimp only [A]
        nlinarith
    rw [PiLp.dist_eq_of_L1]
    calc
      _ ≤ ∑ _c : Σ i, Fin (valueDim (kind i)),
          (((A : ℝ) + (L : ℝ) * S * ((A : ℝ) + 1)) * dist z z') :=
        Finset.sum_le_sum (fun c _ => hcoord c.1 c.2)
      _ = _ := by simp [fixedLabelLipschitzBudget, A, S, mul_assoc]

-- @node: fixedLabelObservation_lipschitz
/-- For [a structural causal model](hyp:M) and [a nonnegative bound](hyp:L)
such that [all continuous mechanisms are Lipschitz with that bound](hyp:hL),
if [an admissible intervention](hyp:t) [assigns every categorical
node](hyp:hcover), then [the complete observation with zero intrinsic noise is
Lipschitz in the joint latent vector, with the recursive budget after the
number of nodes squared plus the number of nodes steps](goal). -/
lemma fixedLabelObservation_lipschitz (M : EuclideanSCM kind dims)
    (L : ℝ≥0) (hL : ContinuousMechanismsLipschitz M L)
    (t : LawIntervention kind)
    (hcover : ∀ i k, kind i = .inr k → t.val i ≠ none) :
    LipschitzWith (fixedLabelLipschitzBudget M L (n*n+n))
      (fixedLabelObservation M t.val) := by
  apply LipschitzWith.of_dist_le_mul
  exact evalSteps_fixed_labels_dist_le M L hL t hcover (n*n+n)

end
end Papers.TbsNeuralCausalPi
