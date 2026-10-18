module
public import Papers.TbsNeuralCausalPi.Helpers.BoxReduction
/-! # The retained output bound controls every intervention history

Continuous outputs obey their full-domain one-norm bound. Categorical outputs
are actual finite labels, so a cube containing all labels bounds them as well.
These bounds apply at every evaluation step, uniformly over bounded assignments.
-/
public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
  {C : Fin b → Set (Fin n)}

-- @node: canonical_nodeValue_coordinate_bound
/-- For [a nonnegative bound K](hyp:K), suppose [every categorical node has
at most K categories](hyp:hlabels) and [every continuous mechanism has output
one-norm at most K throughout its domain](hyp:hcontinuous). If [the structural
input to node i at the given joint state and exogenous realization belongs to
its domain](hyp:hx), then [every coordinate of that node's evaluated value has
absolute value at most K](goal). -/
lemma canonical_nodeValue_coordinate_bound
    (M : CanonicalSCM kind dims dag G C) (K : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (hcontinuous : ∀ i d, kind i = Sum.inl d → ∀ x ∈ M.domain i, ‖M.f i x‖ ≤ K)
    (i : Fin n) (v : Joint kind) (u : Exogenous kind dims)
    (hx : structuralInput M.toEuclideanSCM i v u ∈ M.domain i)
    (j : Fin (valueDim (kind i))) :
    |(nodeValue M.toEuclideanSCM i v u).ofLp j| ≤ K := by
  have hcases : (∃ d, kind i = Sum.inl d) ∨ (∃ k, kind i = Sum.inr k) := by
    cases kind i with
    | inl d => exact Or.inl ⟨d, rfl⟩
    | inr k => exact Or.inr ⟨k, rfl⟩
  rcases hcases with ⟨d, hi⟩ | ⟨k, hi⟩
  ·
    rw [nodeValue_continuous_coordinate M.toEuclideanSCM i d hi,
      canonical_continuousMap_eq M i d hi, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ _).trans (hcontinuous i d hi _ hx)
  ·
    obtain ⟨label, hlabel⟩ := observedValueEmbedding_categorical_label hi
      (M.toEuclideanSCM.f i (structuralInput M.toEuclideanSCM i v u) (categoricalNoise i u))
    have hn : nodeValue M.toEuclideanSCM i v u = observedValueEmbedding (kind i)
        (M.toEuclideanSCM.f i (structuralInput M.toEuclideanSCM i v u)
          (categoricalNoise i u)) := (observedValueEmbedding_eq _ _).symm
    rw [hn, hlabel j, abs_of_nonneg (Nat.cast_nonneg _)]
    exact (by exact_mod_cast Nat.succ_le_of_lt label.isLt :
      ((label.val + 1 : ℕ) : ℝ) ≤ k).trans (hlabels i k hi)

-- @node: canonical_evalSteps_coordinate_bound
/-- For [a nonnegative bound K](hyp:K), if [every categorical node has at most
K categories](hyp:hlabels), [every continuous mechanism has output one-norm at
most K throughout its domain](hyp:hcontinuous), and [every assigned intervention
value has all coordinates bounded in absolute value by K](hyp:ht), then
[every coordinate of every node's value after any number of evaluation steps
is bounded in absolute value by K, for every exogenous realization](goal). -/
lemma canonical_evalSteps_coordinate_bound
    (M : CanonicalSCM kind dims dag G C) (K : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (hcontinuous : ∀ i d, kind i = Sum.inl d → ∀ x ∈ M.domain i, ‖M.f i x‖ ≤ K)
    (t : LawIntervention kind)
    (ht : ∀ i v, t.val i = some v → ∀ j, |v.ofLp j| ≤ K)
    (u : Exogenous kind dims) (r : ℕ) :
    ∀ i j, |(evalSteps M.toEuclideanSCM t.val u r).ofLp ⟨i,j⟩| ≤ K := by
  induction r with
  | zero => intro i j; simpa [evalSteps] using K.coe_nonneg
  | succ r ih =>
    intro i j
    simp only [evalSteps, WithLp.ofLp_toLp]
    by_cases hi : dag.topoOrder i = r
    · simp only [show M.toEuclideanSCM.dag = dag from rfl, hi, if_true]
      cases he : t.val i with
      | some v => simpa only [Option.getD_some] using ht i v he j
      | none =>
        simp only [Option.getD_none]
        exact canonical_nodeValue_coordinate_bound M K hlabels hcontinuous i _ u
          (evalSteps_structuralInput_mem_domain M.toEuclideanSCM t.val t.property u i r hi) j
    · simpa only [show M.toEuclideanSCM.dag = dag from rfl, hi, if_false] using ih i j

-- @node: boxTruncatedSCM_interventionalLaw_eq_of_output_bound
/-- For [a nonnegative bound K](hyp:K), suppose [every categorical node has at
most K categories](hyp:hlabels), [every continuous mechanism has output one-norm
at most K throughout its domain](hyp:hcontinuous), [the model's variables obey
the bound K](hyp:hbound), and [all assigned intervention values have coordinates
bounded in absolute value by K](hyp:ht). Then [truncating the model to the
box of radius K preserves its law under this intervention](goal). -/
lemma boxTruncatedSCM_interventionalLaw_eq_of_output_bound
    (M : CanonicalSCM kind dims dag G C) (K : ℝ≥0)
    (hlabels : ∀ i k, kind i = Sum.inr k → (k : ℝ) ≤ K)
    (hcontinuous : ∀ i d, kind i = Sum.inl d → ∀ x ∈ M.domain i, ‖M.f i x‖ ≤ K)
    (hbound : VariablesBoundedAt M.toEuclideanSCM K)
    (t : LawIntervention kind)
    (ht : ∀ i v, t.val i = some v → ∀ j, |v.ofLp j| ≤ K) :
    interventionalLaw (boxTruncatedSCM M K hlabels).toEuclideanSCM t =
      interventionalLaw M.toEuclideanSCM t := by
  apply Measure.map_congr
  filter_upwards [hbound.2] with u hu
  apply boxTruncatedSCM_evalSteps_eq
  intro r hr i hi
  rintro (⟨p,j⟩ | ⟨a,j⟩)
  · exact canonical_evalSteps_coordinate_bound M K hlabels hcontinuous t ht u r p.val j
  · exact hu.2 a.val j

end
end Papers.TbsNeuralCausalPi
