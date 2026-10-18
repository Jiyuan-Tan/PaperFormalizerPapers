module
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationStep
public import Papers.TbsNeuralCausalPi.Helpers.EvaluationKernels
public import Papers.TbsNeuralCausalPi.Helpers.ApproximationLatents
/-! # Propagation through active topological slots

Empty slots preserve the error. Only slots containing a node contribute a
factor or a local error, giving the node-count exponent in the paper.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

-- @node: approximationActiveCount
/-- For [a finite set of active slots](hyp:slots) and [a stage r](hyp:r), the
[active-update count](goal) is the number of active slots strictly before r. -/
def approximationActiveCount (slots : Finset ℕ) (r : ℕ) : ℕ :=
  ((Finset.range r).filter (fun s => s ∈ slots)).card

-- @node: approximationActiveCount_succ
/-- [The number of active slots before r + 1 equals the number before r,
plus one if r is active and zero otherwise](goal). -/
lemma approximationActiveCount_succ (slots : Finset ℕ) (r : ℕ) :
    approximationActiveCount slots (r + 1) =
      approximationActiveCount slots r + if r ∈ slots then 1 else 0 := by
  classical
  by_cases hr : r ∈ slots <;>
    simp [approximationActiveCount, Finset.range_add_one, Finset.filter_insert, hr]

-- @node: approximationActiveCount_le
/-- [The number of active slots before any stage is at most the total number
of active slots](goal). -/
lemma approximationActiveCount_le (slots : Finset ℕ) (r : ℕ) :
    approximationActiveCount slots r ≤ slots.card := by
  apply Finset.card_le_card
  intro s hs
  exact (Finset.mem_filter.mp hs).2

-- @node: approximation_active_recurrence_le
/-- For [a nonnegative, possibly infinite error sequence E](hyp:E) and
[nonnegative, possibly infinite coefficients A and T](hyp:A,T), suppose
[each active slot increases the error to at most A times its previous value
plus T](hyp:hstep) and [inactive slots preserve the error](hyp:hskip).
Then [the error at r is at most A to the number of preceding active slots
times the initial error, plus T times the sum of powers of A from zero up
to one less than that count](goal). -/
lemma approximation_active_recurrence_le (slots : Finset ℕ)
    (E : ℕ → ℝ≥0∞) (A T : ℝ≥0∞)
    (hstep : ∀ r ∈ slots, E (r + 1) ≤ A * E r + T)
    (hskip : ∀ r, r ∉ slots → E (r + 1) = E r) (r : ℕ) :
    E r ≤ A ^ approximationActiveCount slots r * E 0 +
      T * ∑ s ∈ Finset.range (approximationActiveCount slots r), A^s := by
  classical
  induction r with
  | zero => simp [approximationActiveCount]
  | succ r ih =>
    rw [approximationActiveCount_succ]
    by_cases hr : r ∈ slots
    · simp only [hr, if_true]
      calc
        E (r + 1) ≤ A * E r + T := hstep r hr
        _ ≤ A * (A ^ approximationActiveCount slots r * E 0 +
            T * ∑ s ∈ Finset.range (approximationActiveCount slots r), A^s) + T := by
          gcongr
        _ = _ := by
          rw [Finset.sum_range_succ']
          simp_rw [pow_succ']
          rw [← Finset.mul_sum]
          simp only [pow_zero]
          ring
    · simpa only [hr, if_false, Nat.add_zero, hskip r hr] using ih

-- @node: approximation_active_uniform_bound
/-- For [a nonnegative, possibly infinite error sequence E](hyp:E),
[nonnegative coefficients A and B](hyp:A,B), and [a nonnegative, possibly
infinite structural error S](hyp:S), suppose [A is at least one](hyp:hA),
[each active update gives error at most A times the previous error plus B
times S](hyp:hstep), and [inactive slots preserve the error](hyp:hskip).
If [there are at most N active slots](hyp:hN), then [at every stage r the
error is at most the propagation constant for A, B, and N times the sum of S
and the initial error](goal). -/
lemma approximation_active_uniform_bound (slots : Finset ℕ)
    (E : ℕ → ℝ≥0∞) (A B : ℝ≥0) (S : ℝ≥0∞) (hA : 1 ≤ A)
    (hstep : ∀ r ∈ slots, E (r + 1) ≤ (A : ℝ≥0∞) * E r + (B : ℝ≥0∞) * S)
    (hskip : ∀ r, r ∉ slots → E (r + 1) = E r)
    {N : ℕ} (hN : slots.card ≤ N) (r : ℕ) :
    E r ≤ (approximationPropagationConstant A B N : ℝ≥0∞) * (S + E 0) := by
  let Q : ℕ → ℝ≥0∞ := fun m => (A : ℝ≥0∞)^m * E 0 +
    (B : ℝ≥0∞) * S * ∑ s ∈ Finset.range m, (A : ℝ≥0∞)^s
  have hQ (m : ℕ) : Q (m + 1) ≤ (A : ℝ≥0∞) * Q m + (B : ℝ≥0∞) * S := by
    dsimp only [Q]
    rw [Finset.sum_range_succ']
    simp_rw [pow_succ']
    rw [← Finset.mul_sum]
    simp only [pow_zero]
    apply le_of_eq
    ring
  have hbound := approximation_history_uniform_bound Q A B S hA hQ
    ((approximationActiveCount_le slots r).trans hN)
  have hzero : Q 0 = E 0 := by simp [Q]
  rw [hzero] at hbound
  exact (approximation_active_recurrence_le slots E A ((B : ℝ≥0∞) * S)
    hstep hskip r).trans hbound

-- @node: approximation_topological_uniform_bound
/-- For [a nonnegative, possibly infinite error sequence E](hyp:E),
[nonnegative coefficients A and B](hyp:A,B), and [a nonnegative, possibly infinite
structural error S](hyp:S), suppose [A is at least one](hyp:hA), [each node's
topological update gives error at most A times the previous error plus B times
S](hyp:hstep), and [slots containing no node preserve the error](hyp:hskip).
Then [at every stage the error is at most the propagation constant for A, B,
and the graph's node count times the sum of S and the initial error](goal). -/
lemma approximation_topological_uniform_bound {n : ℕ}
    (dag : Causalean.Graph.DAG (Fin n)) (E : ℕ → ℝ≥0∞)
    (A B : ℝ≥0) (S : ℝ≥0∞) (hA : 1 ≤ A)
    (hstep : ∀ i, E (dag.topoOrder i + 1) ≤
      (A : ℝ≥0∞) * E (dag.topoOrder i) + (B : ℝ≥0∞) * S)
    (hskip : ∀ r, (∀ i, dag.topoOrder i ≠ r) → E (r + 1) = E r) (r : ℕ) :
    E r ≤ (approximationPropagationConstant A B n : ℝ≥0∞) * (S + E 0) := by
  classical
  apply approximation_active_uniform_bound (Finset.univ.image dag.topoOrder)
    E A B S hA
  · intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact hstep i
  · intro s hs
    apply hskip s
    intro i hi
    exact hs (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
  · exact Finset.card_image_le.trans (by simp)

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: approximationHistory
/-- For [a Euclidean structural causal model M](hyp:M), [an intervention t](hyp:t),
[an exogenous realization u](hyp:u), and [an evaluation stage r](hyp:r), the
[augmented history](goal) combines the non-Gumbel latent coordinates of u with
the observed values obtained by evaluating M under t through stage r. -/
def approximationHistory (M : EuclideanSCM kind dims) (t : Intervention kind)
    (u : Exogenous kind dims) (r : ℕ) :
    WithLp 1 (((Σ j, Fin (dims j)) ⊕ (Σ i, Fin (valueDim (kind i)))) → ℝ) :=
  WithLp.toLp 1 (Sum.elim (fun j => u.ofLp (.inl j)) (evalSteps M t u r).ofLp)

-- @node: approximationHistory_measurable
/-- [The augmented history at any fixed evaluation stage of a Euclidean
structural causal model under an intervention is a measurable function of
the exogenous realization](goal). -/
@[fun_prop] lemma approximationHistory_measurable (M : EuclideanSCM kind dims)
    (t : Intervention kind) (r : ℕ) : Measurable (fun u => approximationHistory M t u r) := by
  apply (PiLp.continuous_toLp 1 _).measurable.comp
  apply measurable_pi_lambda
  intro i
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

-- @node: approximationHistory_empty_slot
/-- If [no node occupies topological slot r](hyp:hr), then [advancing evaluation
from r to r + 1 leaves the augmented history unchanged](goal). -/
lemma approximationHistory_empty_slot (M : EuclideanSCM kind dims)
    (t : Intervention kind) (r : ℕ) (hr : ∀ i, M.dag.topoOrder i ≠ r)
    (u : Exogenous kind dims) :
    approximationHistory M t u (r + 1) = approximationHistory M t u r := by
  simp only [approximationHistory, evalSteps_succ_eq_of_empty_slot M t u r hr]

-- @node: approximationHistorySetNode
/-- For [a node i](hyp:i), [a replacement value v for that node](hyp:v), and
[an augmented history x](hyp:x), the [history replacement map](goal) replaces
the observed coordinates of i by v and keeps every other coordinate unchanged. -/
def approximationHistorySetNode (i : Fin n) (v : L1Vec (valueDim (kind i)))
    (x : WithLp 1 (((Σ j, Fin (dims j)) ⊕ (Σ j, Fin (valueDim (kind j)))) → ℝ)) :=
  WithLp.toLp 1 (Sum.elim (fun j => x.ofLp (.inl j)) (fun j : Σ j, Fin (valueDim (kind j)) =>
    if h : j.1 = i then v.ofLp (Fin.cast (congrArg (fun j => valueDim (kind j)) h) j.2)
    else x.ofLp (.inr j)))

-- @node: approximationHistorySetNode_measurable
/-- [Replacing a fixed node's observed value in an augmented history by a
fixed vector is a measurable map](goal). -/
@[fun_prop] lemma approximationHistorySetNode_measurable
    (i : Fin n) (v : L1Vec (valueDim (kind i))) :
    Measurable (approximationHistorySetNode (dims := dims) i v) := by
  apply (PiLp.continuous_toLp 1 _).measurable.comp
  apply measurable_pi_lambda
  intro j
  cases j with
  | inl j =>
    dsimp only [Sum.elim_inl]
    fun_prop
  | inr j =>
    dsimp only [Sum.elim_inr]
    split_ifs <;> fun_prop

-- @node: approximationHistorySetNode_nonexpansive
/-- [Replacing the same node by the same value in two augmented histories
cannot increase their distance in the sum metric](goal). -/
lemma approximationHistorySetNode_nonexpansive
    (i : Fin n) (v : L1Vec (valueDim (kind i)))
    (x y : WithLp 1 (((Σ j, Fin (dims j)) ⊕ (Σ j, Fin (valueDim (kind j)))) → ℝ)) :
    edist (approximationHistorySetNode i v x) (approximationHistorySetNode i v y) ≤
      edist x y := by
  simp only [approximationHistorySetNode, PiLp.edist_eq_of_L1]
  apply Finset.sum_le_sum
  intro j _
  cases j with
  | inl j => exact le_rfl
  | inr j =>
    dsimp only [Sum.elim_inr]
    split_ifs
    · simp only [edist_self]; exact zero_le
    · exact le_rfl

-- @node: approximationHistory_intervened_step_eq
/-- If [the intervention fixes node i to v](hyp:ht), then [the augmented history
after i's topological update equals the preceding history with i's observed
value replaced by v](goal). -/
lemma approximationHistory_intervened_step_eq
    (M : CanonicalSCM kind dims dag G C) (t : Intervention kind)
    (i : Fin n) (v : L1Vec (valueDim (kind i))) (ht : t i = some v)
    (u : Exogenous kind dims) :
    approximationHistory M.toEuclideanSCM t u (dag.topoOrder i + 1) =
      approximationHistorySetNode i v
        (approximationHistory M.toEuclideanSCM t u (dag.topoOrder i)) := by
  classical
  have hdag : M.toEuclideanSCM.dag = dag := rfl
  apply WithLp.ofLp_injective
  funext j
  cases j with
  | inl j => rfl
  | inr j =>
    rcases j with ⟨j,k⟩
    by_cases hj : j = i
    · subst j
      simp [approximationHistory, approximationHistorySetNode, evalSteps, hdag, ht]
    · have horder : dag.topoOrder j ≠ dag.topoOrder i :=
        fun h => hj (dag.topoOrder_injective h)
      simp [approximationHistory, approximationHistorySetNode, evalSteps, hdag, hj, horder]

-- @node: approximationHistory_intervened_step_transport_le
/-- If [the shared intervention fixes node i to v](hyp:ht), then [the
Wasserstein-1 distance between the two models' augmented-history laws after
i's update is at most their distance before that update](goal). -/
lemma approximationHistory_intervened_step_transport_le
    (M Mhat : CanonicalSCM kind dims dag G C) (t : Intervention kind)
    (i : Fin n) (v : L1Vec (valueDim (kind i))) (ht : t i = some v) :
    wasserstein1
      (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t u
        (dag.topoOrder i + 1)))
      (Mhat.latentLaw.map (fun u => approximationHistory Mhat.toEuclideanSCM t u
        (dag.topoOrder i + 1))) ≤
      wasserstein1
        (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t u (dag.topoOrder i)))
        (Mhat.latentLaw.map (fun u => approximationHistory Mhat.toEuclideanSCM t u
          (dag.topoOrder i))) := by
  have h := approximation_wasserstein_map_nonexpansive
    (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t u (dag.topoOrder i)))
    (Mhat.latentLaw.map (fun u => approximationHistory Mhat.toEuclideanSCM t u (dag.topoOrder i)))
    (approximationHistorySetNode i v) (by fun_prop)
    (approximationHistorySetNode_nonexpansive i v)
  rw [Measure.map_map (by fun_prop)
      (approximationHistory_measurable M.toEuclideanSCM t _),
    Measure.map_map (by fun_prop)
      (approximationHistory_measurable Mhat.toEuclideanSCM t _)] at h
  simpa only [Function.comp_def, ← approximationHistory_intervened_step_eq _ t i v ht] using h

-- @node: approximationHistory_initial_transport_le
/-- [The Wasserstein-1 distance between the two models' initial augmented-history
laws under a shared intervention is at most the Wasserstein-1 distance between
their full latent laws](goal). -/
lemma approximationHistory_initial_transport_le
    (M Mhat : CanonicalSCM kind dims dag G C) (t : Intervention kind) :
    wasserstein1
      (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t u 0))
      (Mhat.latentLaw.map (fun u => approximationHistory Mhat.toEuclideanSCM t u 0)) ≤
      wasserstein1 M.latentLaw Mhat.latentLaw := by
  apply approximation_wasserstein_map_nonexpansive _ _
    (fun u => approximationHistory M.toEuclideanSCM t u 0) (by fun_prop)
  intro u v
  simp only [approximationHistory, evalSteps, PiLp.edist_eq_of_L1,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, edist_self, Finset.sum_const_zero, add_zero]
  exact le_add_right le_rfl

-- @node: approximationHistory_observed_transport_le
/-- [At any evaluation stage under a shared intervention, the Wasserstein-1
distance between the two models' observed-value laws is at most the distance
between their augmented-history laws](goal). -/
lemma approximationHistory_observed_transport_le
    (M Mhat : CanonicalSCM kind dims dag G C) (t : Intervention kind) (r : ℕ) :
    wasserstein1
      (M.latentLaw.map (fun u => evalSteps M.toEuclideanSCM t u r))
      (Mhat.latentLaw.map (fun u => evalSteps Mhat.toEuclideanSCM t u r)) ≤
      wasserstein1
        (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t u r))
        (Mhat.latentLaw.map (fun u => approximationHistory Mhat.toEuclideanSCM t u r)) := by
  let project : WithLp 1 (((Σ j, Fin (dims j)) ⊕
      (Σ i, Fin (valueDim (kind i)))) → ℝ) → Joint kind :=
    fun v => WithLp.toLp 1 (fun i => v.ofLp (.inr i))
  have hp : Measurable project := by fun_prop
  have h := approximation_wasserstein_map_nonexpansive
    (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t u r))
    (Mhat.latentLaw.map (fun u => approximationHistory Mhat.toEuclideanSCM t u r))
    project hp (fun v w => by
      simp only [project, PiLp.edist_eq_of_L1, Fintype.sum_sum_type]
      exact le_add_left le_rfl)
  rw [Measure.map_map hp (approximationHistory_measurable M.toEuclideanSCM t r),
    Measure.map_map hp (approximationHistory_measurable Mhat.toEuclideanSCM t r)] at h
  exact h

-- @node: approximation_interventional_bound_of_history_steps
/-- For [nonnegative coefficients A and B](hyp:A,B) and [a nonnegative, possibly
infinite structural error S](hyp:S), suppose [A is at least one](hyp:hA) and
[at each node update the Wasserstein-1 distance between the two models'
augmented-history laws is at most A times its previous value plus B times S](hyp:hstep).
Then [the Wasserstein-1 distance between their interventional laws is at most
the propagation constant for A, B, and the node count times the sum of S and
the Wasserstein-1 distance between their latent laws](goal). -/
lemma approximation_interventional_bound_of_history_steps
    (M Mhat : CanonicalSCM kind dims dag G C) (t : LawIntervention kind)
    (A B : ℝ≥0) (S : ℝ≥0∞) (hA : 1 ≤ A)
    (hstep : ∀ i,
      wasserstein1
        (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t.val u
          (dag.topoOrder i + 1)))
        (Mhat.latentLaw.map (fun u => approximationHistory Mhat.toEuclideanSCM t.val u
          (dag.topoOrder i + 1))) ≤
      (A : ℝ≥0∞) * wasserstein1
        (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t.val u
          (dag.topoOrder i)))
        (Mhat.latentLaw.map (fun u => approximationHistory Mhat.toEuclideanSCM t.val u
          (dag.topoOrder i))) + (B : ℝ≥0∞) * S) :
    wasserstein1 (interventionalLaw M.toEuclideanSCM t)
      (interventionalLaw Mhat.toEuclideanSCM t) ≤
      (approximationPropagationConstant A B n : ℝ≥0∞) *
        (S + wasserstein1 M.latentLaw Mhat.latentLaw) := by
  let E : ℕ → ℝ≥0∞ := fun r => wasserstein1
    (M.latentLaw.map (fun u => approximationHistory M.toEuclideanSCM t.val u r))
    (Mhat.latentLaw.map (fun u => approximationHistory Mhat.toEuclideanSCM t.val u r))
  have hskip (r : ℕ) (hr : ∀ i, dag.topoOrder i ≠ r) : E (r + 1) = E r := by
    dsimp only [E]
    simp only [approximationHistory_empty_slot M.toEuclideanSCM t.val r hr,
      approximationHistory_empty_slot Mhat.toEuclideanSCM t.val r hr]
  calc
    _ ≤ E (n * n + n) := approximationHistory_observed_transport_le M Mhat t.val _
    _ ≤ (approximationPropagationConstant A B n : ℝ≥0∞) * (S + E 0) :=
      approximation_topological_uniform_bound dag E A B S hA hstep hskip _
    _ ≤ _ := by
      gcongr
      exact approximationHistory_initial_transport_le M Mhat t.val

end
end Papers.TbsNeuralCausalPi
