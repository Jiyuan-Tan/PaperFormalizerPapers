module

public import Papers.TbsNeuralCausalPi.Helpers.StructuralProductExtension
/-! # Convex-range extensions of canonical structural functions

A categorical parent has exactly one input coordinate, with one-based labels.
The actual structural domain is therefore the finite-coordinate carrying set
of the product extension theorem.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
open scoped NNReal
noncomputable section
variable {n b : ℕ} {kind : Fin n → NodeKind} {dims : Fin b → ℕ}
  {dag : Causalean.Graph.DAG (Fin n)} {G : SimpleGraph (Fin n)} {C : Fin b → Set (Fin n)}

-- @node: StructuralCoordinate
/-- For [node types](hyp:kind) on [a system of nodes](hyp:n), [latent-block
dimensions](hyp:dims) for [a collection of blocks](hyp:b), [a directed acyclic
graph](hyp:dag), [block-to-node incidence sets](hyp:C), and [a selected
node](hyp:i), [the structural input coordinate type](goal) consists of either
a coordinate of a parent node's value or a coordinate of an incident latent block. -/
abbrev StructuralCoordinate (kind : Fin n → NodeKind) (dims : Fin b → ℕ)
    (dag : Causalean.Graph.DAG (Fin n)) (C : Fin b → Set (Fin n)) (i : Fin n) :=
  Sum (Σ p : {p // p ∈ dag.parents i}, Fin (valueDim (kind p)))
    (Σ j : {j // j ∈ canonicalIncidence C i}, Fin (dims j))

-- @node: structuralCategoricalCoordinates
/-- For [a selected node](hyp:i) among [the system's nodes](hyp:n), with [node
types](hyp:kind), [a parent graph](hyp:dag), and [incidence sets](hyp:C) for
[latent blocks](hyp:b) of [specified dimensions](hyp:dims), [the categorical
coordinate set](goal) contains exactly the input coordinates belonging to
categorical parents and excludes latent-block coordinates. -/
def structuralCategoricalCoordinates (i : Fin n) :
    Finset (StructuralCoordinate kind dims dag C i) := by
  classical
  exact Finset.univ.filter (fun c => match c with
    | .inl ⟨p,_⟩ => (kind p).isRight = true
    | .inr _ => False)

-- @node: structuralCategoricalLastLabel
/-- For [a selected node](hyp:i) among [the system's nodes](hyp:n), with [node
types](hyp:kind), [a parent graph](hyp:dag), and [incidence sets](hyp:C) for
[latent blocks](hyp:b) of [specified dimensions](hyp:dims), [the last-label
index function](goal) assigns [to a parent coordinate, zero for a continuous
parent and the number of categories minus one for a categorical parent](step:1),
and [to a latent-block coordinate, zero](step:2). -/
def structuralCategoricalLastLabel (i : Fin n) :
    StructuralCoordinate kind dims dag C i → ℕ
  | .inl ⟨p,_⟩ => match kind p with
    | .inl _ => 0
    | .inr k => k - 1
  | .inr _ => 0

/-- [The selected canonical structural function's domain equals the product
domain that restricts precisely its categorical parent coordinates to the
one-based labels up to their numbers of categories](goal). -/
-- @node: canonical_domain_eq_structuralProductDomain
lemma canonical_domain_eq_structuralProductDomain
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) :
    M.domain i none = structuralProductDomain (structuralCategoricalCoordinates i)
      (structuralCategoricalLastLabel i) := by
  classical
  ext x
  constructor
  · intro hx c hc
    cases c with
    | inr c => simp [structuralCategoricalCoordinates] at hc
    | inl c =>
      obtain ⟨p,j⟩ := c
      cases hk : kind p.val with
      | inl d => simp [structuralCategoricalCoordinates, hk] at hc
      | inr k =>
        obtain ⟨a, ha⟩ := hx.1 p k hk
        refine ⟨a.val, ?_, ?_⟩
        · simp only [structuralCategoricalLastLabel, hk]
          omega
        · simpa only [Nat.cast_add, Nat.cast_one] using ha j
  · intro hx
    refine ⟨?_, Set.mem_univ _⟩
    intro p k hk
    let j₀ : Fin (valueDim (kind p.val)) := ⟨0, by simp [hk, valueDim]⟩
    have hc : Sum.inl ⟨p,j₀⟩ ∈ structuralCategoricalCoordinates
        (kind := kind) (dims := dims) (dag := dag) (C := C) i := by
      simp [structuralCategoricalCoordinates, hk]
    obtain ⟨a, ha, he⟩ := hx _ hc
    have hp := M.categoricalPositive p.val k hk
    have ha' : a < k := by
      simp only [structuralCategoricalLastLabel, hk] at ha
      omega
    refine ⟨⟨a,ha'⟩, ?_⟩
    intro j
    have hj : j = j₀ := by
      apply Fin.ext
      have hj := j.isLt
      simp only [hk, valueDim] at hj
      exact Nat.eq_zero_of_le_zero (by omega)
    simpa only [hj, Nat.cast_add, Nat.cast_one] using he

/-- For [a nonnegative Lipschitz bound](hyp:L), suppose [the output constraint
set is convex](hyp:hS), [the selected canonical structural function is
Lipschitz with that bound on its domain](hyp:hf), and [its values there lie
in the constraint set](hyp:hrange). Then [a function on the whole input space
exists that is globally Lipschitz with the same bound, takes all its values
in the constraint set, and agrees with the structural function on its domain](goal). -/
-- @node: canonical_convex_structural_extension
lemma canonical_convex_structural_extension
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (L : ℝ≥0)
    {S : Set (L1Vec (outputDim (kind i)))} (hS : Convex ℝ S)
    (hf : LipschitzOnWith L (M.f i) (M.domain i none))
    (hrange : ∀ x ∈ M.domain i none, M.f i x ∈ S) :
    ∃ g : Input kind dims dag C i → L1Vec (outputDim (kind i)),
      LipschitzWith L g ∧ (∀ x, g x ∈ S) ∧ Set.EqOn g (M.f i) (M.domain i none) := by
  classical
  rw [canonical_domain_eq_structuralProductDomain] at hf hrange ⊢
  exact structural_product_extension _ _ (M.f i) hS hf hrange


/-- For [nonnegative Lipschitz and output-norm bounds](hyp:L,K), suppose [the
selected canonical structural function is Lipschitz with the prescribed
constant on its domain](hyp:hf) and [its output norm there is at most the
prescribed bound](hyp:hb). Then [it has an extension to the whole input space
that retains the global Lipschitz constant and output-norm bound and agrees
with the original function on its domain](goal). -/
-- @node: canonical_bounded_vector_structural_extension
lemma canonical_bounded_vector_structural_extension
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (L K : ℝ≥0)
    (hf : LipschitzOnWith L (M.f i) (M.domain i none))
    (hb : ∀ x ∈ M.domain i none, ‖M.f i x‖ ≤ K) :
    ∃ g : Input kind dims dag C i → L1Vec (outputDim (kind i)),
      LipschitzWith L g ∧ (∀ x, ‖g x‖ ≤ K) ∧ Set.EqOn g (M.f i) (M.domain i none) := by
  obtain ⟨g, hg, hb, heq⟩ := canonical_convex_structural_extension M i L
    (convex_closedBall (0 : L1Vec (outputDim (kind i))) (K : ℝ))
    hf (fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right] using hb x hx)
  exact ⟨g, hg, fun x => by simpa only [Metric.mem_closedBall, dist_zero_right] using hb x,
    heq⟩

/-- If [the selected node is categorical with the specified number of
categories](hyp:hi), then for [a nonnegative Lipschitz bound](hyp:L), whenever
[its canonical structural function is Lipschitz with that bound on its
domain](hyp:hf), [it has an extension to the whole input space with the same
global Lipschitz bound, probability-vector outputs everywhere, and agreement
with the original structural function on its domain](goal). -/
-- @node: canonical_simplex_structural_extension
lemma canonical_simplex_structural_extension
    (M : CanonicalSCM kind dims dag G C) (i : Fin n) (k : ℕ) (hi : kind i = Sum.inr k)
    (L : ℝ≥0) (hf : LipschitzOnWith L (M.f i) (M.domain i none)) :
    ∃ g : Input kind dims dag C i → L1Vec (outputDim (kind i)),
      LipschitzWith L g ∧
      (∀ x, (g x).ofLp ∈ probabilitySimplex (outputDim (kind i))) ∧
      Set.EqOn g (M.f i) (M.domain i none) := by
  apply canonical_convex_structural_extension M i L
    ((convex_stdSimplex ℝ (Fin (outputDim (kind i)))).linear_preimage
      (WithLp.linearEquiv 1 ℝ (Fin (outputDim (kind i)) → ℝ)).toLinearMap) hf
  intro x hx
  have hd : outputDim (kind i) = k := congrArg outputDim hi
  have hs := M.simplex i k hi x hx.1
  constructor
  · intro j
    exact hs.1 (Fin.cast hd j)
  · exact ((Equiv.sum_comp (finCongr hd.symm) _).symm).trans hs.2

end
end Papers.TbsNeuralCausalPi
