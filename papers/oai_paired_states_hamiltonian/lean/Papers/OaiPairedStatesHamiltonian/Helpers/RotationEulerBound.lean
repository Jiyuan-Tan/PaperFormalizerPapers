module

public import Papers.OaiPairedStatesHamiltonian.Helpers.SphereMaps
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Euler's upper bound for a connected rotation system, from orthogonal
vertex and facial gradients. This theorem does not assume genus zero. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian
namespace RotationSystem

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
open Classical
attribute [local instance] propDecidable

variable (R : RotationSystem)

/-- [Reversing a directed edge twice returns the original directed edge](goal). -/
lemma edgeInv_twice (d : R.Dart) : R.edgeInv (R.edgeInv d) = d := R.edgeInv_involutive d

-- @node: RotationSystem.edgeOf_eq_iff
/-- [Two directed edges represent the same undirected edge exactly when the second is the
first or its reversal](goal). -/
lemma edgeOf_eq_iff (d e : R.Dart) :
    R.edgeOf d = R.edgeOf e ↔ e = d ∨ e = R.edgeInv d := by
  constructor
  · intro h
    have hs : R.edgeInv.SameCycle d e := Quotient.exact h
    obtain ⟨n, rfl⟩ := hs.exists_nat_pow_eq
    clear h hs
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h | h
      · exact Or.inr (congrArg R.edgeInv h)
      · exact Or.inl ((congrArg R.edgeInv h).trans (R.edgeInv_involutive d))
  · rintro (rfl | rfl)
    · rfl
    · exact Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr
        (Equiv.Perm.SameCycle.refl R.edgeInv d)).symm

-- @node: RotationSystem.faceOrbit_step
/-- [Taking one step around a face leaves the directed edge in the same face orbit](goal). -/
lemma faceOrbit_step (d : R.Dart) :
    orbitOf R.facePerm (R.facePerm d) = orbitOf R.facePerm d := by
  exact Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr
    (Equiv.Perm.SameCycle.refl R.facePerm d))

-- @node: RotationSystem.dart_invariant_constant
/-- In a rotation system with at least one directed edge, if [the underlying graph is
connected](hyp:hR), [a function assigns a value to each directed edge](hyp:g), and its values
are unchanged by [rotation around a vertex](hyp:hrot) and [edge reversal](hyp:hinv), then
[the function has the same value on every directed edge](goal). -/
lemma dart_invariant_constant [Nonempty R.Dart] {β : Type} (hR : R.toSimpleGraph.Connected)
    (g : R.Dart → β) (hrot : ∀ d, g (R.rot d) = g d)
    (hinv : ∀ d, g (R.edgeInv d) = g d) : ∀ d e, g d = g e := by
  have hp (d : R.Dart) (n : ℕ) : g ((R.rot ^ n) d) = g d := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hrot, ih]
  have hfibre (d e : R.Dart) (h : R.vert d = R.vert e) : g d = g e := by
    obtain ⟨n, hn⟩ := ((R.rot_fibre (R.vert d)).2 rfl h.symm).exists_nat_pow_eq
    exact (hp d n).symm.trans (congrArg g hn)
  let label (v : R.Vertex) : β := if h : ∃ d, R.vert d = v then
    g (Classical.choose h) else g (Classical.arbitrary R.Dart)
  have hl (d : R.Dart) : label (R.vert d) = g d := by
    dsimp only [label]
    rw [dif_pos (show ∃ e, R.vert e = R.vert d from ⟨d, rfl⟩)]
    exact hfibre _ d (Classical.choose_spec (show ∃ e, R.vert e = R.vert d from ⟨d, rfl⟩))
  have hwalk {u v : R.Vertex} (p : R.toSimpleGraph.Walk u v) : label u = label v := by
    induction p with
    | nil => rfl
    | cons h p ih =>
      obtain ⟨_, d, hd, he⟩ := h
      have hstep : label (R.vert d) = label (R.head d) := by
        rw [hl, show R.head d = R.vert (R.edgeInv d) from rfl, hl, hinv]
      rw [hd, he] at hstep
      exact hstep.trans ih
  intro d e
  obtain ⟨p⟩ := hR.preconnected (R.vert d) (R.vert e)
  exact (hl d).symm.trans ((hwalk p).trans (hl e))

/-- In [a rotation system](hyp:R), the [vertex gradient](goal) of [real values assigned to
vertices](hyp:a) along [a directed edge](hyp:d) is the value at its head minus the value at
its tail. -/
noncomputable def vertexGradient (a : R.Vertex → ℝ) (d : R.Dart) : ℝ :=
  a (R.head d) - a (R.vert d)
/-- In [a rotation system](hyp:R), the [facial gradient](goal) of [real values assigned to
face orbits](hyp:b) at [a directed edge](hyp:d) is the value on its face orbit minus the
value on the face orbit of its reversal. -/
noncomputable def facialGradient (b : R.FaceOrbit → ℝ) (d : R.Dart) : ℝ :=
  b (orbitOf R.facePerm d) - b (orbitOf R.facePerm (R.edgeInv d))

-- @node: RotationSystem.vertexGradient_inv
/-- For any real values on vertices, [reversing a directed edge negates its vertex
gradient](goal). -/
lemma vertexGradient_inv (a : R.Vertex → ℝ) (d : R.Dart) :
    R.vertexGradient a (R.edgeInv d) = -R.vertexGradient a d := by
  simp only [vertexGradient, head, R.edgeInv_twice, neg_sub]

-- @node: RotationSystem.facialGradient_inv
/-- For any real values on face orbits, [reversing a directed edge negates its facial
gradient](goal). -/
lemma facialGradient_inv (b : R.FaceOrbit → ℝ) (d : R.Dart) :
    R.facialGradient b (R.edgeInv d) = -R.facialGradient b d := by
  simp only [facialGradient, R.edgeInv_twice, neg_sub]

-- @node: RotationSystem.gradients_orthogonal
/-- For any real values on vertices and any real values on face orbits, [the sum over all
directed edges of the product of the vertex and facial gradients is zero](goal). -/
lemma gradients_orthogonal (a : R.Vertex → ℝ) (b : R.FaceOrbit → ℝ) :
    (∑ d : R.Dart, R.vertexGradient a d * R.facialGradient b d) = 0 := by
  have hs : (∑ d : R.Dart, R.vertexGradient a d * b (orbitOf R.facePerm d)) = 0 := by
    have hp := Equiv.sum_comp R.facePerm
      (fun d => a (R.vert d) * b (orbitOf R.facePerm d))
    have hstep (d : R.Dart) : a (R.vert (R.facePerm d)) * b (orbitOf R.facePerm (R.facePerm d)) =
        a (R.head d) * b (orbitOf R.facePerm d) := by
      rw [R.faceOrbit_step]
      change a (R.vert (R.rot (R.edgeInv d))) * _ = _
      rw [R.rot_vertex]
      rfl
    simp_rw [hstep] at hp
    simp only [vertexGradient, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hp
  have hi : (∑ d : R.Dart, R.vertexGradient a d * b (orbitOf R.facePerm (R.edgeInv d))) = 0 := by
    have hp := Equiv.sum_comp R.edgeInv
      (fun d => R.vertexGradient a d * b (orbitOf R.facePerm (R.edgeInv d)))
    simp only [R.vertexGradient_inv, R.edgeInv_twice, neg_mul] at hp
    have hneg : (∑ x : R.Dart, -(R.vertexGradient a x * b (orbitOf R.facePerm x))) = 0 := by
      rw [Finset.sum_neg_distrib, hs, neg_zero]
    exact hp.symm.trans hneg
  simp only [facialGradient, mul_sub, Finset.sum_sub_distrib, hs, hi, sub_self]

-- @node: RotationSystem.vertexGradient_zero_constant
/-- If [the underlying graph is connected](hyp:hR) and [the vertex gradient of a real-valued
vertex assignment is zero on every directed edge](hyp:ha), then [the assignment has the same
value at every vertex](goal). -/
lemma vertexGradient_zero_constant (hR : R.toSimpleGraph.Connected) (a : R.Vertex → ℝ)
    (ha : ∀ d, R.vertexGradient a d = 0) : ∀ u v, a u = a v := by
  have hw {u v : R.Vertex} (p : R.toSimpleGraph.Walk u v) : a u = a v := by
    induction p with
    | nil => rfl
    | cons h p ih =>
      obtain ⟨_, d, hd, he⟩ := h
      have hh := sub_eq_zero.mp (ha d)
      change a (R.head d) = a (R.vert d) at hh
      rw [hd, he] at hh
      exact hh.symm.trans ih
  intro u v
  obtain ⟨p⟩ := hR.preconnected u v
  exact hw p

-- @node: RotationSystem.facialGradient_zero_constant
/-- In a rotation system with at least one directed edge, if [the underlying graph is
connected](hyp:hR) and [the facial gradient of a real-valued face-orbit assignment is zero on
every directed edge](hyp:hb), then [the assignment has the same value on every face orbit](goal). -/
lemma facialGradient_zero_constant [Nonempty R.Dart] (hR : R.toSimpleGraph.Connected)
    (b : R.FaceOrbit → ℝ) (hb : ∀ d, R.facialGradient b d = 0) : ∀ f g, b f = b g := by
  have hi (d : R.Dart) : b (orbitOf R.facePerm (R.edgeInv d)) = b (orbitOf R.facePerm d) :=
    (sub_eq_zero.mp (hb d)).symm
  have hr (d : R.Dart) : b (orbitOf R.facePerm (R.rot d)) = b (orbitOf R.facePerm d) := by
    have h := R.faceOrbit_step (R.edgeInv d)
    change orbitOf R.facePerm (R.rot (R.edgeInv (R.edgeInv d))) = _ at h
    rw [R.edgeInv_involutive] at h
    exact (congrArg b h).trans (hi d)
  intro f g
  obtain ⟨d, rfl⟩ := Quotient.exists_rep f
  obtain ⟨e, rfl⟩ := Quotient.exists_rep g
  exact R.dart_invariant_constant hR (fun d => b (orbitOf R.facePerm d)) hr hi d e

/-- In [a rotation system](hyp:R), the [chosen directed representative](goal) of [an
undirected edge](hyp:e) is a directed edge belonging to that edge's reversal orbit. -/
noncomputable def edgeRepresentative (e : R.Edge) : R.Dart := Classical.choose (Quotient.exists_rep e)
-- @node: RotationSystem.edgeRepresentative_spec
/-- [The undirected edge represented by its chosen directed representative is the original
edge](goal). -/
lemma edgeRepresentative_spec (e : R.Edge) : R.edgeOf (R.edgeRepresentative e) = e :=
  Classical.choose_spec (Quotient.exists_rep e)

/-- For [a rotation system](hyp:R), the [mixed-gradient linear map](goal) takes a pair of
real-valued vertex and face-orbit assignments to edge values by [adding their vertex and
facial gradients at each edge's chosen directed representative](step:1); this rule
[preserves addition](step:2) and [preserves multiplication by real scalars](step:3). -/
noncomputable def mixedGradient : ((R.Vertex → ℝ) × (R.FaceOrbit → ℝ)) →ₗ[ℝ] (R.Edge → ℝ) where
  toFun x e := R.vertexGradient x.1 (R.edgeRepresentative e) +
    R.facialGradient x.2 (R.edgeRepresentative e)
  map_add' x y := by
    funext e
    simp only [vertexGradient, facialGradient, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' c x := by
    funext e
    simp only [vertexGradient, facialGradient, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

-- @node: RotationSystem.mixedGradient_ker_all_darts
/-- If [a pair of vertex and face-orbit assignments has zero mixed gradient on every
undirected edge](hyp:hx), then [the sum of its vertex and facial gradients is zero on any
directed edge](goal). -/
lemma mixedGradient_ker_all_darts (x : ((R.Vertex → ℝ) × (R.FaceOrbit → ℝ)))
    (hx : R.mixedGradient x = 0) (d : R.Dart) :
    R.vertexGradient x.1 d + R.facialGradient x.2 d = 0 := by
  let e := R.edgeOf d
  let r := R.edgeRepresentative e
  have hr : R.edgeOf r = R.edgeOf d := R.edgeRepresentative_spec e
  have hz : R.vertexGradient x.1 r + R.facialGradient x.2 r = 0 := congrFun hx e
  rcases (R.edgeOf_eq_iff r d).mp hr with h | h
  · simpa only [h] using hz
  · rw [h, R.vertexGradient_inv, R.facialGradient_inv]
    linarith

-- @node: RotationSystem.mixedGradient_ker_constants
/-- In a rotation system with at least one directed edge, if [the underlying graph is
connected](hyp:hR) and [a pair of vertex and face-orbit assignments has zero mixed
gradient](hyp:hx), then [the vertex assignment is constant and the face-orbit assignment
is constant](goal). -/
lemma mixedGradient_ker_constants [Nonempty R.Dart] (hR : R.toSimpleGraph.Connected)
    (x : ((R.Vertex → ℝ) × (R.FaceOrbit → ℝ))) (hx : R.mixedGradient x = 0) :
    (∀ u v, x.1 u = x.1 v) ∧ (∀ f g, x.2 f = x.2 g) := by
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
  have hf (d : R.Dart) : R.facialGradient x.2 d = 0 := by
    have hz := hd d
    rw [hv d, zero_add] at hz
    exact hz
  exact ⟨R.vertexGradient_zero_constant hR x.1 hv, R.facialGradient_zero_constant hR x.2 hf⟩

-- @node: RotationSystem.euler_bound
/-- For a rotation system with at least one directed edge, if [the underlying graph is
connected](hyp:hR), then [the number of vertices plus the number of face orbits is at most
the number of edges plus two](goal).

The kernel of the mixed-gradient map consists of the two constant potentials, so its
image has dimension at least the number of vertices plus face orbits minus two. -/
lemma euler_bound [Nonempty R.Dart] (hR : R.toSimpleGraph.Connected) :
    Fintype.card R.Vertex + Fintype.card R.FaceOrbit ≤ Fintype.card R.Edge + 2 := by
  let : Nonempty R.Vertex := hR.nonempty
  let v0 := Classical.arbitrary R.Vertex
  let f0 : R.FaceOrbit := orbitOf R.facePerm (Classical.arbitrary R.Dart)
  let ev : LinearMap.ker R.mixedGradient →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun x => (x.val.1 v0, x.val.2 f0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hevinj : Function.Injective ev := by
    intro x y he
    have hx := R.mixedGradient_ker_constants hR x.val x.property
    have hy := R.mixedGradient_ker_constants hR y.val y.property
    apply Subtype.ext
    apply Prod.ext
    · funext v
      exact (hx.1 v v0).trans ((congrArg Prod.fst he).trans (hy.1 v0 v))
    · funext f
      exact (hx.2 f f0).trans ((congrArg Prod.snd he).trans (hy.2 f0 f))
  have hk := LinearMap.finrank_le_finrank_of_injective hevinj
  have hr := Submodule.finrank_le (R.mixedGradient.range)
  have hn := LinearMap.finrank_range_add_finrank_ker R.mixedGradient
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi] at hk hr hn
  omega

end RotationSystem

end OaiPairedStatesHamiltonian
