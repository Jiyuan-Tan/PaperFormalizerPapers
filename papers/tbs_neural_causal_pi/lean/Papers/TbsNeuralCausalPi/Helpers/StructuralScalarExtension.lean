module
public import Papers.TbsNeuralCausalPi.Helpers.CandidateAssembly
public import Mathlib.Topology.MetricSpace.Lipschitz
/-! # Bounded scalar extensions on actual structural domains

The scalar McShane extension followed by interval clipping preserves the exact
Lipschitz constant and the uniform output one-norm bound. Agreement holds on
the entire actual input domain, including its categorical parent slices.
-/
public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal

-- @node: structural_bounded_real_extension
/-- If [a real-valued function f is L-Lipschitz on s](hyp:hf) and [its
absolute value is at most K on s](hyp:hb), then [there is a globally
L-Lipschitz real-valued function agreeing with f on s and bounded in absolute
value by K everywhere](goal). -/
lemma structural_bounded_real_extension {X : Type*} [PseudoMetricSpace X]
    {s : Set X} {f : X → ℝ} {L K : ℝ≥0}
    (hf : LipschitzOnWith L f s) (hb : ∀ x ∈ s, |f x| ≤ K) :
    ∃ g : X → ℝ, LipschitzWith L g ∧ (∀ x, |g x| ≤ K) ∧ Set.EqOn g f s := by
  obtain ⟨g, hg, heq⟩ := hf.extend_real
  refine ⟨fun x => max (-(K : ℝ)) (min (g x) K),
    (hg.min_const K).const_max (-(K : ℝ)), ?_, ?_⟩
  · intro x
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (neg_le_self K.coe_nonneg) (min_le_right _ _)⟩
  · intro x hx
    change max (-(K : ℝ)) (min (g x) K) = f x
    rw [← heq hx, min_eq_left (abs_le.mp (hb x hx)).2,
      max_eq_right (abs_le.mp (hb x hx)).1]

-- @node: structural_bounded_scalar_extension
/-- If [the output dimension is one](hyp:hd), [f is L-Lipschitz on s](hyp:hf),
and [the one-norm of f is at most K on s](hyp:hb), then [there is a globally
L-Lipschitz vector-valued function agreeing with f on s whose one-norm is at
most K everywhere](goal). -/
lemma structural_bounded_scalar_extension {X : Type*} [PseudoMetricSpace X]
    {d : ℕ} (hd : d = 1) {s : Set X} {f : X → L1Vec d} {L K : ℝ≥0}
    (hf : LipschitzOnWith L f s) (hb : ∀ x ∈ s, ‖f x‖ ≤ K) :
    ∃ g : X → L1Vec d, LipschitzWith L g ∧
      (∀ x, ‖g x‖ ≤ K) ∧ Set.EqOn g f s := by
  subst d
  have hc : LipschitzOnWith L (fun x => (f x).ofLp 0) s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact (PiLp.dist_apply_le (f x) (f y) 0).trans (hf.dist_le_mul x hx y hy)
  obtain ⟨g, hg, hgb, hgeq⟩ := structural_bounded_real_extension hc
    (fun x hx => (PiLp.norm_apply_le (f x) 0).trans (hb x hx))
  refine ⟨fun x => WithLp.toLp 1 (fun _ : Fin 1 => g x), ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [PiLp.dist_eq_of_L1] using hg.dist_le_mul x y
  · intro x
    simpa [PiLp.norm_eq_of_L1, Real.norm_eq_abs] using hgb x
  · intro x hx
    apply PiLp.ext
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hgeq hx

-- @node: canonical_scalar_structural_extension
/-- In [a canonical structural causal model M](hyp:M), consider [a node
i](hyp:i) [with a one-dimensional continuous output](hyp:hi), [a nonnegative
Lipschitz bound L](hyp:L), and [a nonnegative output bound K](hyp:K). If
[the node's mechanism is L-Lipschitz on its full structural input
domain](hyp:hf) and [its output one-norm is at most K there](hyp:hb), then
[there is an extension to the entire ambient input space that is globally
L-Lipschitz, has output one-norm at most K everywhere, and agrees with the
mechanism on its full structural input domain](goal). -/
lemma canonical_scalar_structural_extension
    {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)}
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (hi : kind i = Sum.inl 1)
    (L K : ℝ≥0) (hf : LipschitzOnWith L (M.f i) (M.domain i none))
    (hb : ∀ x ∈ M.domain i none, ‖M.f i x‖ ≤ K) :
    ∃ g : Input kind dims dag C i → L1Vec (outputDim (kind i)),
      LipschitzWith L g ∧ (∀ x, ‖g x‖ ≤ K) ∧ Set.EqOn g (M.f i) (M.domain i none) := by
  have hd : outputDim (kind i) = 1 := by simp [hi, outputDim]
  exact structural_bounded_scalar_extension hd hf hb

-- @node: canonical_domain_eq_univ_of_continuous_parents
/-- In [a canonical structural causal model M](hyp:M), for [a node i](hyp:i),
if [every parent of i has continuous output](hyp:hp), then [the node's full
structural input domain is the entire ambient input space](goal). -/
lemma canonical_domain_eq_univ_of_continuous_parents
    {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
    {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)}
    {C : Fin b → Set (Fin n)}
    (M : CanonicalSCM kind dims dag G C) (i : Fin n)
    (hp : ∀ p ∈ dag.parents i, (kind p).isLeft = true) :
    M.domain i none = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine ⟨?_, Set.mem_univ _⟩
  intro p k hk
  have h := hp p.val p.property
  simp [hk] at h

end Papers.TbsNeuralCausalPi
