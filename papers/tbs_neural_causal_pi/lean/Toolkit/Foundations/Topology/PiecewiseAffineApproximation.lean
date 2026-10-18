module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.Closure
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Toolkit.Foundations.Topology.PiecewiseAffine
public import Toolkit.Foundations.Topology.SimplicialAction
public import Toolkit.Foundations.Topology.SubdivisionMesh

/-!
# Uniform piecewise affine approximation by vertex interpolation

A continuous map on the underlying space of a finite geometric simplicial complex is
uniformly approximated by the piecewise affine map interpolating it at the vertices of a
fine enough iterated barycentric subdivision (uniform continuity on the compact space plus
`mesh_sdIterate_tendsto_zero`). This module provides:

* `originalPoint`, `interpolate` and `SimplicialAction.iterate` (the action on
  `sdIterate Q k`), with `SimplicialAction.iterate_free`;
* `interpolate_eventually_close`: eventually in `k`, the interpolant is uniformly within any
  tolerance of the map;
* `interpolate_equivariant`: the interpolant of an equivariant map is equivariant.
-/

@[expose] public section

namespace Toolkit.Foundations.Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Group G]

/-- For [a complex](hyp:Q) in [a real normed space](hyp:E) and [a number of
subdivisions](hyp:k), the [original point](goal) corresponding to [a point
in that subdivision](hyp:x) has the same ambient coordinates. -/
def originalPoint (Q : Geometry.SimplicialComplex ℝ E) (k : ℕ)
    (x : (sdIterate Q k).space) : Q.space :=
  ⟨x, (sdIterate_space Q k) ▸ x.property⟩

/-- For [a complex](hyp:Q) in [a finite-dimensional real normed space](hyp:E)
and [a function](hyp:f) into [a real normed target space](hyp:F), the
[interpolant on a subdivision](goal) samples the function at all vertices
after [the specified number of subdivisions](hyp:k). -/
noncomputable def interpolate [FiniteDimensional ℝ E]
    (Q : Geometry.SimplicialComplex ℝ E) (f : Q.space → F) (k : ℕ) :
    PLMap (sdIterate Q k) F :=
  PLMap.ofVertices (sdIterate Q k)
    (fun v => f (originalPoint Q k (vertexPoint (sdIterate Q k) v)))

/-- The [iterated action](goal) associated with [a simplicial action](hyp:α)
of [a group](hyp:G) on [a complex](hyp:Q) in [a real normed space](hyp:E)
follows [the number of subdivisions](hyp:k), [starting with the original
action](step:1) and [subdividing it at each step](step:2). -/
noncomputable def SimplicialAction.iterate {Q : Geometry.SimplicialComplex ℝ E}
    (α : SimplicialAction G Q) : (k : ℕ) → SimplicialAction G (sdIterate Q k)
  | 0 => α
  | k + 1 => (α.iterate k).subdivide

/-- If [a simplicial action is free on the realization](hyp:hfree), [its action
on every iterated subdivision is free](goal). -/
theorem SimplicialAction.iterate_free {Q : Geometry.SimplicialComplex ℝ E}
    {α : SimplicialAction G Q} (hfree : α.IsFree) (k : ℕ) : (α.iterate k).IsFree := by
  have haction : ∀ n, (α.iterate n).action = α.action := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact ih
  intro g x hx
  apply hfree g (originalPoint Q k x)
  apply Subtype.ext
  have h := congrArg Subtype.val hx
  change (α.iterate k).action g x = x at h
  change α.action g (x : E) = (x : E)
  simpa only [haction] using h

/-- If [a complex has finitely many faces](hyp:hQ), [a function on it is
continuous](hyp:hf), and [the tolerance is positive](hyp:hε), [all sufficiently
fine vertex interpolants approximate it within that tolerance everywhere](goal). -/
theorem interpolate_eventually_close [FiniteDimensional ℝ E]
    {Q : Geometry.SimplicialComplex ℝ E} (hQ : Q.faces.Finite)
    {f : Q.space → F} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in Filter.atTop, ∀ x : (sdIterate Q k).space,
      dist (interpolate Q f k x) (f (originalPoint Q k x)) < ε := by
  classical
  let : CompactSpace Q.space := isCompact_iff_compactSpace.mp (isCompact_space hQ)
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) ε hε
  have hmesh : ∀ᶠ k in Filter.atTop, mesh (sdIterate Q k) < δ :=
    (mesh_sdIterate_tendsto_zero hQ).eventually (gt_mem_nhds hδ)
  filter_upwards [hmesh] with k hk
  intro x
  obtain ⟨s, hs, hx⟩ := (sdIterate Q k).mem_space_iff.mp x.property
  obtain ⟨a, ha⟩ := (interpolate Q f k).affine_on_face s hs
  have hvertices : (s : Set E) ⊆ a ⁻¹' Metric.ball (f (originalPoint Q k x)) ε := by
    intro p hp
    have hpQ : p ∈ (sdIterate Q k).vertices := by
      rw [(sdIterate Q k).vertices_eq]
      exact Set.mem_iUnion₂.mpr ⟨s, hs, hp⟩
    have hpc := subset_convexHull ℝ (s : Set E) hp
    have hav : a p = f (originalPoint Q k (vertexPoint (sdIterate Q k) ⟨p, hpQ⟩)) :=
      (ha p hpc).symm.trans (PLMap.ofVertices_vertex _ _ ⟨p, hpQ⟩)
    change dist (a p) (f (originalPoint Q k x)) < ε
    rw [hav]
    apply hclose
    change dist p (x : E) < δ
    have hd := Metric.dist_le_diam_of_mem
      (isBounded_convexHull.mpr s.finite_toSet.isBounded) hpc hx
    have hm : Metric.diam (convexHull ℝ (s : Set E)) ≤ mesh (sdIterate Q k) :=
      le_csSup (((sdIterate_finite hQ k).image _).insert 0).bddAbove
        (Set.mem_insert_of_mem _ ⟨s, hs, rfl⟩)
    exact (hd.trans hm).trans_lt hk
  have hxball := convexHull_min hvertices
    ((convex_ball (f (originalPoint Q k x)) ε).affine_preimage a) hx
  change dist (a x) (f (originalPoint Q k x)) < ε at hxball
  rw [ha x hx]
  exact hxball

/-- If [a function is equivariant](hyp:hf) for [a simplicial action](hyp:α) and
[a linear representation](hyp:ρ), [its interpolant on each iterated subdivision
is equivariant](goal). -/
theorem interpolate_equivariant [FiniteDimensional ℝ E]
    {Q : Geometry.SimplicialComplex ℝ E} (α : SimplicialAction G Q)
    (ρ : G →* (F ≃ₗ[ℝ] F)) {f : Q.space → F} (hf : Equivariant α ρ f) (k : ℕ) :
    Equivariant (α.iterate k) ρ (interpolate Q f k) := by
  have haction : ∀ n, (α.iterate n).action = α.action := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact ih
  apply PLMap.ofVertices_equivariant
  intro g p
  have hpoint : originalPoint Q k (vertexPoint (sdIterate Q k)
      ((α.iterate k).onVertices g p)) =
      α.onSpace g (originalPoint Q k (vertexPoint (sdIterate Q k) p)) := by
    apply Subtype.ext
    change (α.iterate k).action g p = α.action g p
    rw [haction]
  change f (originalPoint Q k (vertexPoint (sdIterate Q k)
    ((α.iterate k).onVertices g p))) = _
  rw [hpoint]
  exact hf g _

end Toolkit.Foundations.Topology
