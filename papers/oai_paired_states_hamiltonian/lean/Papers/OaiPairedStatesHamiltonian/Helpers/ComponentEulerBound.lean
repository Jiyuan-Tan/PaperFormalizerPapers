module

public import Papers.OaiPairedStatesHamiltonian.Helpers.RotationEulerBound

/-! Euler's upper bound with all components and puncture boundaries retained.
The kernel has two constant potentials per component, including an isolated
vertex together with its puncture. No genus hypothesis is used in the bound. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian
namespace RotationSystem

set_option linter.style.openClassical false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable
variable (R : RotationSystem)

-- @node: RotationSystem.vertexGradient_zero_sameComponent
/-- If [a real vertex potential has zero difference along every dart](hyp:ha) and
[two vertices belong to the same connected component](hyp:hc), then
[the potential takes the same value at those vertices](goal). -/
lemma vertexGradient_zero_sameComponent (a : R.Vertex → ℝ)
    (ha : ∀ d, R.vertexGradient a d = 0) (u v : R.Vertex)
    (hc : R.toSimpleGraph.connectedComponentMk u = R.toSimpleGraph.connectedComponentMk v) :
    a u = a v := by
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hc
  clear hc
  induction p with
  | nil => rfl
  | cons h p ih =>
    obtain ⟨_, d, hd, he⟩ := h
    have hh := sub_eq_zero.mp (ha d)
    change a (R.head d) = a (R.vert d) at hh
    rw [hd, he] at hh
    exact hh.symm.trans ih

-- @node: RotationSystem.dart_invariant_sameComponent
/-- If [a dart labeling is unchanged by rotation around a vertex](hyp:hrot) and
[by reversal across an edge](hyp:hinv), and [two darts have vertices in the same
connected component](hyp:hc), then [their labels agree](goal). -/
lemma dart_invariant_sameComponent {β : Type} (g : R.Dart → β)
    (hrot : ∀ d, g (R.rot d) = g d) (hinv : ∀ d, g (R.edgeInv d) = g d)
    (d e : R.Dart)
    (hc : R.toSimpleGraph.connectedComponentMk (R.vert d) =
      R.toSimpleGraph.connectedComponentMk (R.vert e)) : g d = g e := by
  have hp (x : R.Dart) (n : ℕ) : g ((R.rot ^ n) x) = g x := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hrot, ih]
  have hfibre (x y : R.Dart) (h : R.vert x = R.vert y) : g x = g y := by
    obtain ⟨n, hn⟩ := ((R.rot_fibre (R.vert x)).2 rfl h.symm).exists_nat_pow_eq
    exact (hp x n).symm.trans (congrArg g hn)
  let label (v : R.Vertex) : β := if h : ∃ x, R.vert x = v then
    g (Classical.choose h) else g d
  have hl (x : R.Dart) : label (R.vert x) = g x := by
    dsimp only [label]
    rw [dif_pos (show ∃ y, R.vert y = R.vert x from ⟨x, rfl⟩)]
    exact hfibre _ x (Classical.choose_spec (show ∃ y, R.vert y = R.vert x from ⟨x, rfl⟩))
  have hw {u v : R.Vertex} (p : R.toSimpleGraph.Walk u v) : label u = label v := by
    induction p with
    | nil => rfl
    | cons h p ih =>
      obtain ⟨_, x, hx, hy⟩ := h
      have hs : label (R.vert x) = label (R.head x) := by
        rw [hl, show R.head x = R.vert (R.edgeInv x) from rfl, hl, hinv]
      rw [hx, hy] at hs
      exact hs.trans ih
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hc
  exact (hl d).symm.trans ((hw p).trans (hl e))

-- @node: RotationSystem.facialGradient_zero_sameComponent
/-- If [a real face-orbit potential has zero difference across every dart](hyp:hb)
and [two face orbits belong to the same component](hyp:hc), then
[their potential values agree](goal). -/
lemma facialGradient_zero_sameComponent (b : R.FaceOrbit → ℝ)
    (hb : ∀ d, R.facialGradient b d = 0) (f g : R.FaceOrbit)
    (hc : R.orbitComponent f = R.orbitComponent g) : b f = b g := by
  have hi (d : R.Dart) : b (orbitOf R.facePerm (R.edgeInv d)) = b (orbitOf R.facePerm d) :=
    (sub_eq_zero.mp (hb d)).symm
  have hr (d : R.Dart) : b (orbitOf R.facePerm (R.rot d)) = b (orbitOf R.facePerm d) := by
    have h := R.faceOrbit_step (R.edgeInv d)
    change orbitOf R.facePerm (R.rot (R.edgeInv (R.edgeInv d))) = _ at h
    rw [R.edgeInv_involutive] at h
    exact (congrArg b h).trans (hi d)
  obtain ⟨d, rfl⟩ := Quotient.exists_rep f
  obtain ⟨e, rfl⟩ := Quotient.exists_rep g
  exact R.dart_invariant_sameComponent (fun d => b (orbitOf R.facePerm d)) hr hi d e hc

-- @node: RotationSystem.puncture_component_vertex
/-- If [an isolated vertex represented by a puncture and another vertex belong to
the same connected component](hyp:hc), then [they are the same vertex](goal). -/
lemma puncture_component_vertex (v : R.Puncture) (w : R.Vertex)
    (hc : R.toSimpleGraph.connectedComponentMk v.val = R.toSimpleGraph.connectedComponentMk w) :
    v.val = w := by
  by_contra hne
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hc
  obtain ⟨_, d, hd, _⟩ := p.adj_snd (p.not_nil_of_ne hne)
  exact v.property d hd

-- @node: RotationSystem.boundaryPotential_zero_sameComponent
/-- If [a real potential on local boundaries has zero facial gradient on every dart](hyp:hb)
and [two local boundaries belong to the same component](hyp:hc), then
[their potential values agree](goal). -/
lemma boundaryPotential_zero_sameComponent (b : R.LocalBoundary → ℝ)
    (hb : ∀ d, R.facialGradient (fun f => b (Sum.inl f)) d = 0)
    (x y : R.LocalBoundary) (hc : R.compOf x = R.compOf y) : b x = b y := by
  cases x with
  | inl f =>
    cases y with
    | inl g => exact R.facialGradient_zero_sameComponent _ hb f g hc
    | inr v =>
      obtain ⟨d, rfl⟩ := Quotient.exists_rep f
      exact False.elim (v.property d (R.puncture_component_vertex v (R.vert d) hc.symm).symm)
  | inr v =>
    cases y with
    | inl g =>
      obtain ⟨d, rfl⟩ := Quotient.exists_rep g
      exact False.elim (v.property d (R.puncture_component_vertex v (R.vert d) hc).symm)
    | inr w =>
      have hv := R.puncture_component_vertex v w.val hc
      exact congrArg b (congrArg Sum.inr (Subtype.ext hv))

-- @node: RotationSystem.componentVertexRepresentative
/-- For [a rotation system](hyp:R) and [one of its connected components](hyp:K),
[the component's vertex representative](goal) is an arbitrarily chosen vertex in that component. -/
noncomputable def componentVertexRepresentative (K : R.Component) : R.Vertex :=
  Classical.choose K.exists_rep

-- @node: RotationSystem.componentVertexRepresentative_spec
/-- [The chosen vertex representative of a connected component belongs to that component](goal). -/
lemma componentVertexRepresentative_spec (K : R.Component) :
    R.toSimpleGraph.connectedComponentMk (R.componentVertexRepresentative K) = K :=
  Classical.choose_spec K.exists_rep

-- @node: RotationSystem.componentBoundaryRepresentative
/-- For [a rotation system](hyp:R) and [a connected component](hyp:K),
[the component's local boundary representative](goal) is [the face orbit of a chosen dart
at its representative vertex, if such a dart exists](step:1), or [the puncture at that
isolated representative vertex otherwise](step:2). -/
noncomputable def componentBoundaryRepresentative (K : R.Component) : R.LocalBoundary :=
  if h : ∃ d, R.vert d = R.componentVertexRepresentative K then
    Sum.inl (orbitOf R.facePerm (Classical.choose h))
  else Sum.inr ⟨R.componentVertexRepresentative K, fun d hd => h ⟨d, hd⟩⟩

-- @node: RotationSystem.componentBoundaryRepresentative_spec
/-- [The chosen local boundary representative of a connected component belongs to that component](goal). -/
lemma componentBoundaryRepresentative_spec (K : R.Component) :
    R.compOf (R.componentBoundaryRepresentative K) = K := by
  unfold componentBoundaryRepresentative
  split_ifs with h
  · change R.toSimpleGraph.connectedComponentMk (R.vert (Classical.choose h)) = K
    rw [Classical.choose_spec h]
    exact R.componentVertexRepresentative_spec K
  · exact R.componentVertexRepresentative_spec K

-- @node: RotationSystem.mixedGradient_ker_gradients_zero
/-- If [a pair of real vertex and face-orbit potentials has zero mixed gradient](hyp:hx),
then [its vertex gradient and its facial gradient both vanish on every dart](goal). -/
lemma mixedGradient_ker_gradients_zero (x : ((R.Vertex → ℝ) × (R.FaceOrbit → ℝ)))
    (hx : R.mixedGradient x = 0) :
    (∀ d, R.vertexGradient x.1 d = 0) ∧ (∀ d, R.facialGradient x.2 d = 0) := by
  have hd := R.mixedGradient_ker_all_darts x hx
  have hsum : (∑ d : R.Dart, (R.vertexGradient x.1 d) ^ 2) = 0 := by
    have hz : (∑ d : R.Dart, R.vertexGradient x.1 d *
        (R.vertexGradient x.1 d + R.facialGradient x.2 d)) = 0 := by simp [hd]
    simp only [mul_add, Finset.sum_add_distrib, R.gradients_orthogonal, add_zero] at hz
    simpa only [pow_two] using hz
  have hv (d : R.Dart) : R.vertexGradient x.1 d = 0 := by
    have hp : (R.vertexGradient x.1 d) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun d _ => sq_nonneg (R.vertexGradient x.1 d))).mp
        hsum d (Finset.mem_univ _)
    exact sq_eq_zero_iff.mp hp
  refine ⟨hv, ?_⟩
  intro d
  have hz := hd d
  rw [hv d, zero_add] at hz
  exact hz

-- @node: RotationSystem.boundaryMixedGradient
/-- For [a rotation system](hyp:R), [the boundary mixed-gradient linear map](goal)
sends a vertex potential and a local-boundary potential to edge values by adding
the vertex gradient to the facial gradient of the boundary potential restricted to
face orbits; puncture values do not contribute. -/
noncomputable def boundaryMixedGradient :
    ((R.Vertex → ℝ) × (R.LocalBoundary → ℝ)) →ₗ[ℝ] (R.Edge → ℝ) where
  toFun x := R.mixedGradient (x.1, fun f => x.2 (Sum.inl f))
  map_add' x y := by
    funext e
    simp only [mixedGradient, vertexGradient, facialGradient, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  map_smul' c x := by
    funext e
    simp only [mixedGradient, vertexGradient, facialGradient, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring

-- @node: RotationSystem.euler_bound_all_components
/-- [The number of vertices plus the number of local boundaries is at most the
number of edges plus twice the number of connected components](goal), including
isolated vertices and their puncture boundaries. -/
lemma euler_bound_all_components :
    Fintype.card R.Vertex + Fintype.card R.LocalBoundary ≤
      Fintype.card R.Edge + 2 * Fintype.card R.Component := by
  let ev : LinearMap.ker R.boundaryMixedGradient →ₗ[ℝ]
      ((R.Component → ℝ) × (R.Component → ℝ)) :=
    { toFun := fun x => (fun K => x.val.1 (R.componentVertexRepresentative K),
          fun K => x.val.2 (R.componentBoundaryRepresentative K))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hevinj : Function.Injective ev := by
    intro x y he
    have hx := R.mixedGradient_ker_gradients_zero
      (x.val.1, fun f => x.val.2 (Sum.inl f)) x.property
    have hy := R.mixedGradient_ker_gradients_zero
      (y.val.1, fun f => y.val.2 (Sum.inl f)) y.property
    apply Subtype.ext
    apply Prod.ext
    · funext v
      let K := R.toSimpleGraph.connectedComponentMk v
      have hK : R.toSimpleGraph.connectedComponentMk v =
          R.toSimpleGraph.connectedComponentMk (R.componentVertexRepresentative K) :=
        (R.componentVertexRepresentative_spec K).symm
      exact (R.vertexGradient_zero_sameComponent x.val.1 hx.1 _ _ hK).trans
        ((congrFun (congrArg Prod.fst he) K).trans
          (R.vertexGradient_zero_sameComponent y.val.1 hy.1 _ _ hK).symm)
    · funext b
      let K := R.compOf b
      have hK : R.compOf b = R.compOf (R.componentBoundaryRepresentative K) :=
        (R.componentBoundaryRepresentative_spec K).symm
      exact (R.boundaryPotential_zero_sameComponent x.val.2 hx.2 _ _ hK).trans
        ((congrFun (congrArg Prod.snd he) K).trans
          (R.boundaryPotential_zero_sameComponent y.val.2 hy.2 _ _ hK).symm)
  have hk := LinearMap.finrank_le_finrank_of_injective hevinj
  have hr := Submodule.finrank_le (R.boundaryMixedGradient.range)
  have hn := LinearMap.finrank_range_add_finrank_ker R.boundaryMixedGradient
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi] at hk hr hn
  omega

-- @node: RotationSystem.componentEuler_global_card
/-- If [Euler's formula holds in each connected component](hyp:hR), then
[the total number of vertices plus local boundaries equals the total number of
edges plus twice the number of connected components](goal). -/
lemma componentEuler_global_card (hR : R.componentEuler) :
    Nat.card R.Vertex + Nat.card R.LocalBoundary = Nat.card R.Edge + 2 * Nat.card R.Component := by
  have fiber_card {α β : Type} [Fintype α] [Fintype β] (g : α → β) :
      (∑ b, Fintype.card {a // g a = b}) = Fintype.card α := by
    simp_rw [Fintype.card_subtype]
    simpa using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset α) (Finset.univ : Finset β) g
  have he := congrArg (fun f : R.Component → ℕ => ∑ K, f K) (funext hR)
  simp only [Finset.sum_add_distrib, fiber_card, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at he
  simpa only [Nat.card_eq_fintype_card, Nat.mul_comm] using he

end RotationSystem
end OaiPairedStatesHamiltonian
