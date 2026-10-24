module

public import Papers.OaiPairedStatesHamiltonian.Helpers.ComponentEulerBound

/-! Euler bounds on individual component fibres and recovery of componentwise
Euler equality from the global count. Potentials are extended by zero, so the
argument also retains the puncture of an isolated vertex. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian
namespace RotationSystem

set_option linter.style.openClassical false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable
variable (R : RotationSystem)

-- @node: RotationSystem.fiberPotentialExtension
/-- For [a map assigning labels to elements](hyp:g) and [a chosen label](hyp:k),
the [linear extension by zero](goal) sends a real-valued function on the elements
with that label to a function on all elements, assigning zero elsewhere. -/
noncomputable def fiberPotentialExtension {α β : Type} (g : α → β) (k : β) :
    ({a // g a = k} → ℝ) →ₗ[ℝ] (α → ℝ) :=
  Function.ExtendByZero.linearMap ℝ Subtype.val

-- @node: RotationSystem.fiberPotentialExtension_apply
/-- For [a labeling map](hyp:g), [a chosen label](hyp:k), [a real-valued function
on the elements with that label](hyp:f), and [an element with that label](hyp:a),
[extension by zero preserves the function's value at that element](goal). -/
lemma fiberPotentialExtension_apply {α β : Type} (g : α → β) (k : β)
    (f : {a // g a = k} → ℝ) (a : {a // g a = k}) :
    fiberPotentialExtension g k f a.val = f a :=
  Function.Injective.extend_apply Subtype.val_injective f 0 a

-- @node: RotationSystem.fiberPotentialExtension_zero
/-- For [a labeling map](hyp:g), [a chosen label](hyp:k), [a real-valued function
on the elements with that label](hyp:f), and [an element](hyp:a), if
[the element has a different label](hyp:ha), then [the extended function is zero
at that element](goal). -/
lemma fiberPotentialExtension_zero {α β : Type} (g : α → β) (k : β)
    (f : {a // g a = k} → ℝ) (a : α) (ha : g a ≠ k) :
    fiberPotentialExtension g k f a = 0 := by
  apply Function.extend_apply'
  rintro ⟨b, rfl⟩
  exact ha b.property

-- @node: RotationSystem.componentPotentialExtension
/-- For [a rotation system](hyp:R) and [one of its connected components](hyp:K),
the [linear extension of component potentials](goal) extends both vertex and local
boundary potentials to the whole system by assigning zero outside the component. -/
noncomputable def componentPotentialExtension (K : R.Component) :
    (({v // R.toSimpleGraph.connectedComponentMk v = K} → ℝ) ×
      ({b // R.compOf b = K} → ℝ)) →ₗ[ℝ] ((R.Vertex → ℝ) × (R.LocalBoundary → ℝ)) :=
  (fiberPotentialExtension R.toSimpleGraph.connectedComponentMk K).prodMap
    (fiberPotentialExtension R.compOf K)

-- @node: RotationSystem.componentMixedGradient
/-- For [a rotation system](hyp:R) and [one of its connected components](hyp:K),
the [component mixed gradient](goal) is the linear map from vertex and local boundary
potentials on that component to edge values, obtained by extending the potentials
by zero and evaluating the mixed gradient on the component's edges. -/
noncomputable def componentMixedGradient (K : R.Component) :
    (({v // R.toSimpleGraph.connectedComponentMk v = K} → ℝ) ×
      ({b // R.compOf b = K} → ℝ)) →ₗ[ℝ] ({e // R.edgeComponent e = K} → ℝ) where
  toFun x e := R.boundaryMixedGradient (R.componentPotentialExtension K x) e.val
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' c x := by
    simp only [map_smul]
    rfl

-- @node: RotationSystem.componentMixedGradient_outside
/-- In a rotation system, take [a connected component](hyp:K),
[vertex and local boundary potentials on that component](hyp:x), and [an edge](hyp:e).
If [the edge belongs to a different component](hyp:he), then [the mixed gradient
of the potentials extended by zero vanishes on that edge](goal). -/
lemma componentMixedGradient_outside (K : R.Component)
    (x : ({v // R.toSimpleGraph.connectedComponentMk v = K} → ℝ) ×
      ({b // R.compOf b = K} → ℝ)) (e : R.Edge) (he : R.edgeComponent e ≠ K) :
    R.boundaryMixedGradient (R.componentPotentialExtension K x) e = 0 := by
  let d := R.edgeRepresentative e
  have hd : R.toSimpleGraph.connectedComponentMk (R.vert d) ≠ K := by
    have h : R.edgeComponent (R.edgeOf d) = R.edgeComponent e :=
      congrArg R.edgeComponent (R.edgeRepresentative_spec e)
    change R.toSimpleGraph.connectedComponentMk (R.vert d) = R.edgeComponent e at h
    exact fun hc => he (h.symm.trans hc)
  have hh : R.toSimpleGraph.connectedComponentMk (R.head d) ≠ K := by
    rwa [← R.dart_component_eq_head d]
  change fiberPotentialExtension _ K x.1 (R.head d) -
      fiberPotentialExtension _ K x.1 (R.vert d) +
    (fiberPotentialExtension _ K x.2 (Sum.inl (orbitOf R.facePerm d)) -
      fiberPotentialExtension _ K x.2 (Sum.inl (orbitOf R.facePerm (R.edgeInv d)))) = 0
  rw [fiberPotentialExtension_zero _ _ _ _ hh,
    fiberPotentialExtension_zero _ _ _ _ hd,
    fiberPotentialExtension_zero R.compOf K x.2 (Sum.inl (orbitOf R.facePerm d)) hd,
    fiberPotentialExtension_zero R.compOf K x.2 (Sum.inl (orbitOf R.facePerm (R.edgeInv d))) hh]
  ring

-- @node: RotationSystem.componentMixedGradient_ker_global
/-- In a rotation system, for [a connected component](hyp:K) and
[vertex and local boundary potentials on it](hyp:x), if [their component mixed
gradient is zero](hyp:hx), then [their extensions by zero have zero mixed gradient
on the entire system](goal). -/
lemma componentMixedGradient_ker_global (K : R.Component)
    (x : ({v // R.toSimpleGraph.connectedComponentMk v = K} → ℝ) ×
      ({b // R.compOf b = K} → ℝ)) (hx : R.componentMixedGradient K x = 0) :
    R.boundaryMixedGradient (R.componentPotentialExtension K x) = 0 := by
  funext e
  by_cases he : R.edgeComponent e = K
  · exact congrFun hx ⟨e, he⟩
  · exact R.componentMixedGradient_outside K x e he

-- @node: RotationSystem.euler_bound_component
/-- In a rotation system, for [any connected component](hyp:K),
[the number of vertices plus the number of local boundaries in that component
is at most its number of edges plus two](goal). -/
lemma euler_bound_component (K : R.Component) :
    Fintype.card {v // R.toSimpleGraph.connectedComponentMk v = K} +
      Fintype.card {b // R.compOf b = K} ≤
        Fintype.card {e // R.edgeComponent e = K} + 2 := by
  let v0 : {v // R.toSimpleGraph.connectedComponentMk v = K} :=
    ⟨R.componentVertexRepresentative K, R.componentVertexRepresentative_spec K⟩
  let b0 : {b // R.compOf b = K} :=
    ⟨R.componentBoundaryRepresentative K, R.componentBoundaryRepresentative_spec K⟩
  let ev : LinearMap.ker (R.componentMixedGradient K) →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun x => (x.val.1 v0, x.val.2 b0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have constants (x : LinearMap.ker (R.componentMixedGradient K)) :
      (∀ v, x.val.1 v = x.val.1 v0) ∧ (∀ b, x.val.2 b = x.val.2 b0) := by
    have hz := R.componentMixedGradient_ker_global K x.val x.property
    have hg := R.mixedGradient_ker_gradients_zero
      ((R.componentPotentialExtension K x.val).1,
        fun f => (R.componentPotentialExtension K x.val).2 (Sum.inl f)) hz
    constructor
    · intro v
      have hv := R.vertexGradient_zero_sameComponent _ hg.1 v.val v0.val
        (v.property.trans v0.property.symm)
      change fiberPotentialExtension _ K x.val.1 v.val =
        fiberPotentialExtension _ K x.val.1 v0.val at hv
      simpa only [fiberPotentialExtension_apply] using hv
    · intro b
      have hb := R.boundaryPotential_zero_sameComponent
        (R.componentPotentialExtension K x.val).2 hg.2 b.val b0.val
        (b.property.trans b0.property.symm)
      change fiberPotentialExtension _ K x.val.2 b.val =
        fiberPotentialExtension _ K x.val.2 b0.val at hb
      simpa only [fiberPotentialExtension_apply] using hb
  have hevinj : Function.Injective ev := by
    intro x y he
    apply Subtype.ext
    apply Prod.ext
    · funext v
      exact ((constants x).1 v).trans ((congrArg Prod.fst he).trans ((constants y).1 v).symm)
    · funext b
      exact ((constants x).2 b).trans ((congrArg Prod.snd he).trans ((constants y).2 b).symm)
  have hk := LinearMap.finrank_le_finrank_of_injective hevinj
  have hr := Submodule.finrank_le (R.componentMixedGradient K).range
  have hn := LinearMap.finrank_range_add_finrank_ker (R.componentMixedGradient K)
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi] at hk hr hn
  omega

-- @node: RotationSystem.componentEuler_of_global_card
/-- For a rotation system, if [the total number of vertices plus local
boundaries equals the number of edges plus twice the number of connected
components](hyp:hglobal), then [in every component the number of vertices plus
local boundaries equals the number of edges plus two](goal). -/
lemma componentEuler_of_global_card
    (hglobal : Nat.card R.Vertex + Nat.card R.LocalBoundary =
      Nat.card R.Edge + 2 * Nat.card R.Component) : R.componentEuler := by
  have fiber_card {α β : Type} [Fintype α] [Fintype β] (g : α → β) :
      (∑ b, Fintype.card {a // g a = b}) = Fintype.card α := by
    simp_rw [Fintype.card_subtype]
    simpa using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset α) (Finset.univ : Finset β) g
  let lhs (K : R.Component) :=
    Fintype.card {v // R.toSimpleGraph.connectedComponentMk v = K} +
      Fintype.card {b // R.compOf b = K}
  let rhs (K : R.Component) := Fintype.card {e // R.edgeComponent e = K} + 2
  have hle (K) : lhs K ≤ rhs K := R.euler_bound_component K
  have hs : (∑ K, lhs K) = ∑ K, rhs K := by
    simp only [lhs, rhs, Finset.sum_add_distrib, fiber_card, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    simpa only [Nat.card_eq_fintype_card, Nat.mul_comm] using hglobal
  intro K
  change lhs K = rhs K
  by_contra hne
  have hlt : lhs K < rhs K := lt_of_le_of_ne (hle K) hne
  have hsum := Finset.sum_lt_sum (fun J (_ : J ∈ (Finset.univ : Finset R.Component)) => hle J)
    ⟨K, Finset.mem_univ K, hlt⟩
  exact (ne_of_lt hsum) hs

end RotationSystem
end OaiPairedStatesHamiltonian
