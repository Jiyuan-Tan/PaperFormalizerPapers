module
public import Papers.TbsNeuralCausalPi.Helpers.FixedLabelEvaluation
public import Papers.TbsNeuralCausalPi.Helpers.ObservationalPushforwardSampling
public import Mathlib.MeasureTheory.Function.Floor
/-! # The actual finite categorical strata of a canonical evaluation

The decoder is total and measurable on the ambient observation space. On
actual observations it recovers exactly the encoded finite labels. Each
stratum's complete observation is the fixed-label latent readout, with one
Lipschitz budget for all strata.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}

/-- For [a specification of each node's type](hyp:kind), [a complete categorical
stratum](goal) assigns each node a zero-based label, with as many labels as its
categorical noise dimension and a single dummy label when that dimension is zero. -/
-- @node: CategoricalStratum
abbrev CategoricalStratum (kind : Fin n → NodeKind) :=
  ∀ i, Fin (max 1 (noiseDim (kind i)))

/-- For [a joint numerical observation](hyp:v), [the decoded complete categorical
stratum](goal) uses each node's first coordinate when available: take its
nonnegative integer floor, subtract one with truncation at zero, and reduce
modulo the larger of one and the node's categorical noise dimension; nodes
without coordinates receive label zero. -/
-- @node: observedCategoricalStratum
def observedCategoricalStratum (v : Joint kind) : CategoricalStratum kind :=
  fun i => ⟨(if h : 0 < valueDim (kind i) then
      (⌊v.ofLp ⟨i, ⟨0, h⟩⟩⌋₊ - 1) else 0) % max 1 (noiseDim (kind i)),
    Nat.mod_lt _ (by omega)⟩

/-- [Decoding a joint numerical observation into its complete categorical stratum
is a measurable operation](goal). -/
-- @node: observedCategoricalStratum_measurable
@[fun_prop] lemma observedCategoricalStratum_measurable :
    Measurable (observedCategoricalStratum : Joint kind → CategoricalStratum kind) := by
  unfold observedCategoricalStratum
  apply measurable_pi_lambda
  intro i
  apply (measurable_of_countable (fun j : ℕ =>
    (⟨j % max 1 (noiseDim (kind i)), Nat.mod_lt _ (by omega)⟩ :
      Fin (max 1 (noiseDim (kind i)))))).comp
  by_cases h : 0 < valueDim (kind i)
  · simp only [h, dite_true]
    fun_prop
  · simp only [h, dite_false]
    fun_prop

/-- For [a complete categorical stratum](hyp:c), [the corresponding intervention](goal)
[leaves nodes with zero categorical noise dimension untouched](step:1) and
[sets every coordinate of each remaining node to one plus its stratum label](step:2). -/
-- @node: categoricalStratumAssignment
def categoricalStratumAssignment (c : CategoricalStratum kind) : Intervention kind :=
  fun i => if noiseDim (kind i) = 0 then none else
    some (WithLp.toLp 1 (fun _ => (((c i).val + 1 : ℕ) : ℝ)))

/-- [The intervention that fixes the categorical labels of any complete stratum
is admissible for the structural causal model](goal). -/
-- @node: categoricalStratumAssignment_admissible
lemma categoricalStratumAssignment_admissible (M : EuclideanSCM kind dims)
    (c : CategoricalStratum kind) :
    AdmissibleIntervention kind (categoricalStratumAssignment c) := by
  intro i v hv
  split
  · trivial
  · rename_i k hi
    have hk := M.categoricalPositive i k hi
    have hc : (c i).val < k := by
      simpa [hi, noiseDim, max_eq_right (show 1 ≤ k by omega)] using (c i).isLt
    have he : v = WithLp.toLp 1 (fun _ => (((c i).val + 1 : ℕ) : ℝ)) := by
      simpa [categoricalStratumAssignment, hi, noiseDim, Nat.ne_of_gt hk] using hv.symm
    exact ⟨⟨(c i).val, hc⟩, fun j => by rw [he]⟩

/-- If [node i is categorical with k categories](hyp:hi), [the intervention
associated with any complete categorical stratum assigns a value to that node](goal). -/
-- @node: categoricalStratumAssignment_covers
lemma categoricalStratumAssignment_covers (M : EuclideanSCM kind dims)
    (c : CategoricalStratum kind) (i : Fin n) (k : ℕ) (hi : kind i = .inr k) :
    categoricalStratumAssignment c i ≠ none := by
  simp [categoricalStratumAssignment, hi, noiseDim,
    Nat.ne_of_gt (M.categoricalPositive i k hi)]

/-- If [node i is categorical with k categories](hyp:hi) and [all its numerical
coordinates encode the given label as one plus that label](hyp:hv), [decoding
the joint observation recovers that label at node i](goal). -/
-- @node: observedCategoricalStratum_recovers_label
lemma observedCategoricalStratum_recovers_label (v : Joint kind)
    (i : Fin n) (k : ℕ) (hi : kind i = .inr k) (label : Fin k)
    (hv : ∀ j, v.ofLp ⟨i, j⟩ = (label.val + 1 : ℕ)) :
    (observedCategoricalStratum v i).val = label.val := by
  have hk : 1 ≤ k := by have := label.isLt; omega
  have hp : 0 < valueDim (kind i) := by simp [hi, valueDim]
  have hcount : max 1 (noiseDim (kind i)) = k := by simp [hi, noiseDim, hk]
  dsimp only [observedCategoricalStratum]
  rw [dif_pos hp, hv, hcount]
  simp only [Nat.floor_natCast, Nat.add_sub_cancel, Nat.mod_eq_of_lt label.isLt]

/-- If [the intervention obtained from the decoded factual stratum assigns
the vector v to node i](hyp:hv), [every coordinate of v agrees with the factual
observation at that node](goal). -/
-- @node: categoricalStratumAssignment_matches_factual
lemma categoricalStratumAssignment_matches_factual (M : EuclideanSCM kind dims)
    (u : Exogenous kind dims) (i : Fin n) (v : L1Vec (valueDim (kind i)))
    (hv : categoricalStratumAssignment
      (observedCategoricalStratum (intervenedEval M (fun _ => none) u)) i = some v) :
    ∀ j, v.ofLp j = (intervenedEval M (fun _ => none) u).ofLp ⟨i, j⟩ := by
  have hcases : (∃ d, kind i = .inl d) ∨ (∃ k, kind i = .inr k) := by
    cases kind i with
    | inl d => exact Or.inl ⟨d, rfl⟩
    | inr k => exact Or.inr ⟨k, rfl⟩
  rcases hcases with ⟨d, hi⟩ | ⟨k, hi⟩
  · simp [categoricalStratumAssignment, hi, noiseDim] at hv
  · obtain ⟨label, hlabel⟩ := evalSteps_categorical_label M u i k hi (n*n+n)
      (scm_topoOrder_lt_horizon M i)
    have hc := observedCategoricalStratum_recovers_label
      (intervenedEval M (fun _ => none) u) i k hi label hlabel
    have he : v = WithLp.toLp 1 (fun _ => ((label.val + 1 : ℕ) : ℝ)) := by
      simpa [categoricalStratumAssignment, hi, noiseDim, hc,
        Nat.ne_of_gt (M.categoricalPositive i k hi)] using hv.symm
    intro j
    rw [he]
    exact (hlabel j).symm

/-- [At every exogenous input, the factual joint observation equals the fixed-label
readout evaluated at the decoded factual stratum and the joint non-Gumbel
latent vector](goal). -/
-- @node: factual_eq_fixedLabelObservation_stratum
lemma factual_eq_fixedLabelObservation_stratum (M : EuclideanSCM kind dims)
    (u : Exogenous kind dims) :
    intervenedEval M (fun _ => none) u =
      fixedLabelObservation M (categoricalStratumAssignment
        (observedCategoricalStratum (intervenedEval M (fun _ => none) u)))
        (jointNonGumbel u) := by
  symm
  exact fixedLabelObservation_eq_factual M _ (categoricalStratumAssignment_covers M _)
    u (categoricalStratumAssignment_matches_factual M u)

/-- For [a nonnegative constant L](hyp:L), if [the continuous mechanisms of the
model are Lipschitz with constant L](hyp:hL),
[the fixed-label observation map for any complete categorical stratum is
Lipschitz with the model's fixed-label budget at the evaluation horizon](goal). -/
-- @node: categoricalStratumObservation_lipschitz
lemma categoricalStratumObservation_lipschitz (M : EuclideanSCM kind dims)
    (L : ℝ≥0) (hL : ContinuousMechanismsLipschitz M L) (c : CategoricalStratum kind) :
    LipschitzWith (fixedLabelLipschitzBudget M L (n*n+n))
      (fixedLabelObservation M (categoricalStratumAssignment c)) := by
  exact fixedLabelObservation_lipschitz M L hL
    ⟨_, categoricalStratumAssignment_admissible M c⟩ (categoricalStratumAssignment_covers M c)

/-- [The observational law conditional on a complete categorical stratum is the
distribution of the fixed-label readout applied to the joint non-Gumbel latent
vector, whose law is obtained by conditioning the exogenous law on that same
observed stratum](goal).

The conditional joint latent law need not factor over blocks. -/
-- @node: categoricalStratum_conditional_observation_law
lemma categoricalStratum_conditional_observation_law (M : EuclideanSCM kind dims)
    (c : CategoricalStratum kind) :
    cond (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) =
      ((cond M.latentLaw ((observedCategoricalStratum ∘
        intervenedEval M (fun _ => none)) ⁻¹' {c})).map jointNonGumbel).map
          (fixedLabelObservation M (categoricalStratumAssignment c)) := by
  let := M.probability
  exact fixed_label_conditional_observation_law M.latentLaw
    (intervenedEval M (fun _ => none)) jointNonGumbel (by fun_prop [intervenedEval])
    (by fun_prop) observedCategoricalStratum (by fun_prop)
    (fun c => fixedLabelObservation M (categoricalStratumAssignment c))
    (by intro c; fun_prop) (Filter.Eventually.of_forall
      (factual_eq_fixedLabelObservation_stratum M)) c

/-- If [a complete categorical stratum has nonzero observational probability](hyp:hc),
[the joint non-Gumbel latent law conditional on that observed stratum is a
probability measure](goal). -/
-- @node: categoricalStratum_conditional_latent_probability
lemma categoricalStratum_conditional_latent_probability (M : EuclideanSCM kind dims)
    (c : CategoricalStratum kind)
    (hc : (observationalLaw M) (observedCategoricalStratum ⁻¹' {c}) ≠ 0) :
    IsProbabilityMeasure ((cond M.latentLaw ((observedCategoricalStratum ∘
      intervenedEval M (fun _ => none)) ⁻¹' {c})).map jointNonGumbel) := by
  let := M.probability
  exact fixed_label_conditional_latent_probability M.latentLaw
    (intervenedEval M (fun _ => none)) jointNonGumbel (by fun_prop [intervenedEval])
    (by fun_prop) observedCategoricalStratum (by fun_prop) c hc

/-- If [K is positive and the model's observed and non-Gumbel latent coordinates
are almost surely bounded in absolute value by K](hyp:hK),
[every coordinate of the joint non-Gumbel latent vector remains bounded in
absolute value by K almost surely under its law conditional on any complete
observed categorical stratum](goal). -/
-- @node: categoricalStratum_conditional_latent_ae_box
lemma categoricalStratum_conditional_latent_ae_box (M : EuclideanSCM kind dims)
    (K : ℝ) (hK : VariablesBoundedAt M K) (c : CategoricalStratum kind) :
    ∀ᵐ z ∂((cond M.latentLaw ((observedCategoricalStratum ∘
      intervenedEval M (fun _ => none)) ⁻¹' {c})).map jointNonGumbel),
        ∀ a, |z.ofLp a| ≤ K := by
  have hbox : MeasurableSet {z : Latent dims | ∀ a, |z.ofLp a| ≤ K} := by
    have he : {z : Latent dims | ∀ a, |z.ofLp a| ≤ K} =
        ⋂ a, {z : Latent dims | |z.ofLp a| ≤ K} := by ext z; simp
    rw [he]
    exact MeasurableSet.iInter (fun a => measurableSet_le (by fun_prop) measurable_const)
  apply (ae_map_iff (by fun_prop) hbox).mpr
  filter_upwards [cond_absolutelyContinuous.ae_le hK.2] with u hu
  rintro ⟨j,k⟩
  exact hu.2 j k

end
end Papers.TbsNeuralCausalPi
