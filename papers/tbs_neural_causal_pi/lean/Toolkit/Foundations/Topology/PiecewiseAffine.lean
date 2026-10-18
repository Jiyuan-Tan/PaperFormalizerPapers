module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.IsEmpty.Basic
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.Closure
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

/-!
# Piecewise affine maps on a geometric simplicial complex

A map from the underlying space of a geometric simplicial complex to a real normed space is
piecewise affine (`PLMap`) when it agrees with an affine map on every face. This module
provides:

* `isCompact_space` (a finite complex has compact underlying space) and
  `PLMap.continuous`;
* `exists_affine_extension`: values at affinely independent points extend to an affine map;
* `PLMap.ofVertices`, the interpolant of a vertex assignment, with
  `PLMap.ofVertices_vertex` and uniqueness `PLMap.ext_vertices`;
* `PLMap.dist_ofVertices_lt`: interpolants of uniformly close vertex values are uniformly
  close.

Interpolants are glued from affine combinations on faces; they agree on intersections by
the complex's intersection axiom (Rourke–Sanderson, *Introduction to Piecewise-Linear
Topology*, Ch. 2).
-/

@[expose] public section

namespace Toolkit.Foundations.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A [piecewise affine map](goal) from [a geometric complex](hyp:Q) in
[a real normed space](hyp:E) to
[a normed real vector space](hyp:F) has [a value at each point](step:1) and
[agrees with an affine map on every face](step:2). -/
structure PLMap (Q : Geometry.SimplicialComplex ℝ E) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- A [piecewise affine map](hyp:self) from [a complex](hyp:Q) in
  [a real normed space](hyp:E) to [a target vector space](hyp:F) supplies
  [a function on the realization](goal). -/
  toFun : Q.space → F
  /-- For [a piecewise affine map](hyp:self), [a finite vertex set](hyp:s)
  that [is a face](hyp:hs) [has an ambient affine extension agreeing with
  the map](goal) at [every point in that face's convex hull](hyp:x,hx). -/
  affine_on_face : ∀ (s : Finset E) (hs : s ∈ Q.faces), ∃ a : E →ᵃ[ℝ] F,
    ∀ (x : E) (hx : x ∈ convexHull ℝ (s : Set E)),
      toFun ⟨x, Q.convexHull_subset_space hs hx⟩ = a x

/-- For [a complex](hyp:Q) in [a real normed space](hyp:E) and
[a target vector space](hyp:F), [piecewise affine maps can be evaluated as
ordinary functions](goal). -/
instance (Q : Geometry.SimplicialComplex ℝ E) : CoeFun (PLMap Q F) (fun _ => Q.space → F) :=
  ⟨PLMap.toFun⟩

/-- A [vertex](hyp:v) of [a complex](hyp:Q) in [a real normed space](hyp:E)
determines [a point of its underlying space](goal). -/
def vertexPoint (Q : Geometry.SimplicialComplex ℝ E) (v : Q.vertices) : Q.space :=
  ⟨v, Q.vertices_subset_space v.property⟩

/-- If [a complex has finitely many faces](hyp:hQ), [its underlying space is
compact](goal). -/
theorem isCompact_space {Q : Geometry.SimplicialComplex ℝ E} (hQ : Q.faces.Finite) :
    IsCompact Q.space := by
  exact hQ.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull ℝ

/-- If [a complex has finitely many faces](hyp:hQ), [each map affine on its
faces](hyp:g) [is continuous](goal). -/
theorem PLMap.continuous {Q : Geometry.SimplicialComplex ℝ E}
    [FiniteDimensional ℝ E] (hQ : Q.faces.Finite) (g : PLMap Q F) : Continuous g := by
  classical
  let : Finite Q.faces := hQ.to_subtype
  let C : Q.faces → Set Q.space := fun s =>
    Subtype.val ⁻¹' convexHull ℝ (s.val : Set E)
  have hclosed (s : Q.faces) : IsClosed (C s) :=
    s.val.finite_toSet.isCompact_convexHull ℝ |>.isClosed.preimage continuous_subtype_val
  have hcover : (⋃ s, C s) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨s, hs, hx⟩ := Q.mem_space_iff.mp x.property
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hx⟩
  apply (locallyFinite_of_finite C).continuous hcover hclosed
  intro s
  obtain ⟨a, ha⟩ := g.affine_on_face s.val s.property
  apply (a.continuous_of_finiteDimensional.comp continuous_subtype_val).continuousOn.congr
  intro x hx
  exact ha x hx

/-- If [finitely many points are affinely independent](hyp:hs), [any assigned
values at those points](hyp:v) [extend to an affine map on the ambient space](goal). -/
theorem exists_affine_extension [FiniteDimensional ℝ E] {s : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (v : s → F) :
    ∃ a : E →ᵃ[ℝ] F, ∀ p : s, a p = v p := by
  classical
  by_cases hempty : IsEmpty s
  · exact ⟨AffineMap.const ℝ E 0, fun p => (hempty.false p).elim⟩
  · have : Nonempty s := not_isEmpty_iff.mp hempty
    let p₀ : s := Classical.choice inferInstance
    let w : {p : s // p ≠ p₀} → E := fun p => (p.val : E) - p₀
    have hw : LinearIndependent ℝ w :=
      (affineIndependent_iff_linearIndependent_vsub ℝ _ p₀).mp hs
    let b := Module.Basis.extend hw.linearIndepOn_id
    let L : E →ₗ[ℝ] F := b.constr ℝ
      (fun i => Function.extend w (fun p => v p.val - v p₀) (fun _ => 0) i.val)
    have hL (p : {p : s // p ≠ p₀}) : L (w p) = v p.val - v p₀ := by
      let i : hw.linearIndepOn_id.extend (Set.subset_univ _) :=
        ⟨w p, hw.linearIndepOn_id.subset_extend _ ⟨p, rfl⟩⟩
      have hi : b i = w p := Module.Basis.extend_apply_self _ i
      rw [← hi, Module.Basis.constr_basis]
      exact hw.injective.extend_apply _ _ p
    refine ⟨AffineMap.mk' (fun x => L (x - p₀) + v p₀) L (p₀ : E)
      (fun x => by simp), ?_⟩
    intro p
    change L ((p : E) - p₀) + v p₀ = v p
    by_cases hp : p = p₀
    · subst p
      simp
    · rw [show (p : E) - p₀ = w ⟨p, hp⟩ from rfl, hL]
      exact sub_add_cancel _ _

/-- Any [assignment of values to the vertices](hyp:v) of [a complex](hyp:Q)
[extends to a map affine on each face](goal). -/
theorem exists_interpolant [FiniteDimensional ℝ E]
    (Q : Geometry.SimplicialComplex ℝ E) (v : Q.vertices → F) :
    ∃ g : PLMap Q F, ∀ p : Q.vertices, g (vertexPoint Q p) = v p := by
  classical
  have vertex_mem (s : Q.faces) (p : s.val) : (p : E) ∈ Q.vertices := by
    rw [Q.vertices_eq]
    exact Set.mem_iUnion₂.mpr ⟨s.val, s.property, p.property⟩
  choose a ha using fun s : Q.faces =>
    exists_affine_extension (Q.indep s.property)
      (fun p => v ⟨p, vertex_mem s p⟩)
  have agree (s t : Q.faces) (x : E)
      (hs : x ∈ convexHull ℝ (s.val : Set E))
      (ht : x ∈ convexHull ℝ (t.val : Set E)) : a s x = a t x := by
    have hx : x ∈ convexHull ℝ ((s.val : Set E) ∩ (t.val : Set E)) := by
      rw [← Q.convexHull_inter_convexHull s.property t.property]
      exact ⟨hs, ht⟩
    apply AffineMap.eqOn_affineSpan (s := (s.val : Set E) ∩ (t.val : Set E)) ?_
      (convexHull_subset_affineSpan (𝕜 := ℝ) _ hx)
    intro p hp
    exact (ha s ⟨p, hp.1⟩).trans (ha t ⟨p, hp.2⟩).symm
  have face (x : Q.space) : ∃ s : Q.faces, (x : E) ∈ convexHull ℝ (s.val : Set E) := by
    obtain ⟨s, hs, hx⟩ := Q.mem_space_iff.mp x.property
    exact ⟨⟨s, hs⟩, hx⟩
  choose c hc using face
  let g : PLMap Q F :=
    { toFun := fun x => a (c x) x
      affine_on_face := by
        intro s hs
        refine ⟨a ⟨s, hs⟩, ?_⟩
        intro x hx
        exact agree _ _ x (hc _) hx }
  refine ⟨g, ?_⟩
  intro p
  change a (c (vertexPoint Q p)) p = v p
  have hpvertices := p.property
  simp only [Q.vertices_eq, Set.mem_iUnion] at hpvertices
  obtain ⟨s, hs, hp⟩ := hpvertices
  exact (agree _ ⟨s, hs⟩ p (hc _) (subset_convexHull ℝ _ hp)).trans
    (ha ⟨s, hs⟩ ⟨p, hp⟩)

/-- If [two piecewise affine maps](hyp:g,h) [agree at every vertex](hyp:hvertices), then [they
agree at every point](goal). -/
theorem PLMap.ext_vertices {Q : Geometry.SimplicialComplex ℝ E} {g h : PLMap Q F}
    (hvertices : ∀ p : Q.vertices, g (vertexPoint Q p) = h (vertexPoint Q p)) :
    g = h := by
  have hfun : g.toFun = h.toFun := by
    funext x
    obtain ⟨s, hs, hx⟩ := Q.mem_space_iff.mp x.property
    obtain ⟨a, ha⟩ := g.affine_on_face s hs
    obtain ⟨b, hb⟩ := h.affine_on_face s hs
    have hab : Set.EqOn a b (s : Set E) := by
      intro p hp
      have hpQ : p ∈ Q.vertices := by
        rw [Q.vertices_eq]
        exact Set.mem_iUnion₂.mpr ⟨s, hs, hp⟩
      have hpc : p ∈ convexHull ℝ (s : Set E) := subset_convexHull ℝ _ hp
      exact (ha p hpc).symm.trans ((hvertices ⟨p, hpQ⟩).trans (hb p hpc))
    exact (ha x hx).trans ((AffineMap.eqOn_affineSpan hab
      (convexHull_subset_affineSpan (𝕜 := ℝ) (s : Set E) hx)).trans (hb x hx).symm)
  cases g
  cases h
  cases hfun
  rfl

/-- The [vertex interpolant](goal) for [a complex](hyp:Q) in [a finite-dimensional
real normed space](hyp:E) and [a vertex assignment](hyp:v) into [a real normed
target space](hyp:F) is the unique map affine on faces with those vertex values. -/
noncomputable def PLMap.ofVertices [FiniteDimensional ℝ E]
    (Q : Geometry.SimplicialComplex ℝ E) (v : Q.vertices → F) : PLMap Q F :=
  Classical.choose (exists_interpolant Q v)

/-- The interpolant for [a complex](hyp:Q) and [a vertex assignment](hyp:v)
[takes the assigned value at each vertex](goal). -/
theorem PLMap.ofVertices_vertex [FiniteDimensional ℝ E]
    (Q : Geometry.SimplicialComplex ℝ E) (v : Q.vertices → F) (p : Q.vertices) :
    PLMap.ofVertices Q v (vertexPoint Q p) = v p :=
  Classical.choose_spec (exists_interpolant Q v) p

/-- If [two vertex assignments are everywhere less than a tolerance
apart](hyp:h), [their interpolants are less than that tolerance apart at
every point](goal). -/
theorem PLMap.dist_ofVertices_lt [FiniteDimensional ℝ E]
    {Q : Geometry.SimplicialComplex ℝ E} {v w : Q.vertices → F} {ε : ℝ}
    (h : ∀ p, dist (v p) (w p) < ε) (x : Q.space) :
    dist (PLMap.ofVertices Q v x) (PLMap.ofVertices Q w x) < ε := by
  obtain ⟨s, hs, hx⟩ := Q.mem_space_iff.mp x.property
  obtain ⟨a, ha⟩ := (PLMap.ofVertices Q v).affine_on_face s hs
  obtain ⟨b, hb⟩ := (PLMap.ofVertices Q w).affine_on_face s hs
  have hvertices : (s : Set E) ⊆ (a - b) ⁻¹' Metric.ball 0 ε := by
    intro p hp
    have hpQ : p ∈ Q.vertices := by
      rw [Q.vertices_eq]
      exact Set.mem_iUnion₂.mpr ⟨s, hs, hp⟩
    have hpc := subset_convexHull ℝ (s : Set E) hp
    have hav : a p = v ⟨p, hpQ⟩ :=
      (ha p hpc).symm.trans (PLMap.ofVertices_vertex Q v ⟨p, hpQ⟩)
    have hbw : b p = w ⟨p, hpQ⟩ :=
      (hb p hpc).symm.trans (PLMap.ofVertices_vertex Q w ⟨p, hpQ⟩)
    change dist (a p - b p) 0 < ε
    rw [hav, hbw, dist_eq_norm, sub_zero, ← dist_eq_norm]
    exact h ⟨p, hpQ⟩
  have hxball := convexHull_min hvertices ((convex_ball (0 : F) ε).affine_preimage (a - b)) hx
  change dist (a x - b x) 0 < ε at hxball
  rw [ha x hx, hb x hx]
  simpa only [dist_eq_norm, sub_zero] using hxball

end Toolkit.Foundations.Topology
