module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.Closure
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Toolkit.Foundations.Topology.EquivariantGeneralPosition
public import Toolkit.Foundations.Topology.PiecewiseAffine
public import Toolkit.Foundations.Topology.PiecewiseAffineApproximation
public import Toolkit.Foundations.Topology.SimplicialAction
public import Toolkit.Foundations.Topology.SubdivisionMesh

/-!
# Equivariant piecewise affine approximation transverse to zero

A piecewise affine map is transverse to zero (`PLMap.TransverseToZero`) when at each zero
in a face it is affine on that face with linear part mapping the directions of the face onto
the whole target; faces of dimension below the target dimension then miss zero
(`PLMap.TransverseToZero.ne_zero_of_card`). The main result,
`exists_equivariant_transverse_approximation`, is the general-position step of the
configuration-space / test-map method (Matoušek, *Using the Borsuk–Ulam Theorem*, §5.4):
for a free simplicial action of a finite group on a finite complex and a linear
representation on a finite-dimensional target (for instance `Fin n → ℝ`), every continuous
equivariant map is uniformly within any tolerance of an equivariant piecewise affine map,
on some iterated barycentric subdivision, that is transverse to zero there.
-/

@[expose] public section

namespace Toolkit.Foundations.Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Group G]

/-- A [piecewise affine map](hyp:g) from [a complex](hyp:Q) in [a real
normed space](hyp:E) to [a target space](hyp:F) is [transverse to zero](goal)
if at each zero in any face there is an affine extension that [agrees with
the map on that face](step:1) and [maps the linear directions along that
face onto the whole target space](step:2). -/
def PLMap.TransverseToZero {Q : Geometry.SimplicialComplex ℝ E} (g : PLMap Q F) : Prop :=
  ∀ (s : Finset E) (hs : s ∈ Q.faces) (x : E)
    (hx : x ∈ convexHull ℝ (s : Set E)),
    g ⟨x, Q.convexHull_subset_space hs hx⟩ = 0 →
    ∃ a : E →ᵃ[ℝ] F,
      (∀ (y : E) (hy : y ∈ convexHull ℝ (s : Set E)),
        g ⟨y, Q.convexHull_subset_space hs hy⟩ = a y) ∧
      ∀ z : F, ∃ v ∈ (affineSpan ℝ (s : Set E)).direction, a.linear v = z

/-- If [vertex values are in general position relative to zero](hyp:hv),
[their interpolant is transverse to zero](goal). -/
theorem PLMap.ofVertices_transverse [FiniteDimensional ℝ E]
    {Q : Geometry.SimplicialComplex ℝ E} {v : Q.vertices → F}
    (hv : VertexGeneralPosition Q v) : (PLMap.ofVertices Q v).TransverseToZero := by
  intro s hs x hx hz
  obtain ⟨a, ha⟩ := (PLMap.ofVertices Q v).affine_on_face s hs
  have himage : a '' (s : Set E) = v '' {p : Q.vertices | (p : E) ∈ s} := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hpQ : p ∈ Q.vertices := by
        rw [Q.vertices_eq]
        exact Set.mem_iUnion₂.mpr ⟨s, hs, hp⟩
      refine ⟨⟨p, hpQ⟩, hp, ?_⟩
      exact (PLMap.ofVertices_vertex Q v ⟨p, hpQ⟩).symm.trans
        (ha p (subset_convexHull ℝ _ hp))
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      exact (ha p (subset_convexHull ℝ _ hp)).symm.trans
        (PLMap.ofVertices_vertex Q v p)
  have hzero : (0 : F) ∈ affineSpan ℝ (a '' (s : Set E)) := by
    have hax : a x = 0 := (ha x hx).symm.trans hz
    rw [← AffineSubspace.map_span]
    exact hax ▸ AffineSubspace.mem_map.mpr
      ⟨x, convexHull_subset_affineSpan (𝕜 := ℝ) _ hx, rfl⟩
  have htop : affineSpan ℝ (a '' (s : Set E)) = ⊤ := by
    rw [himage] at hzero ⊢
    exact hv s hs hzero
  have hdir : (affineSpan ℝ (s : Set E)).direction.map a.linear = ⊤ := by
    rw [← AffineSubspace.map_direction, AffineSubspace.map_span, htop,
      AffineSubspace.direction_top]
  refine ⟨a, ha, fun z => ?_⟩
  have hzmem : z ∈ (affineSpan ℝ (s : Set E)).direction.map a.linear := by
    rw [hdir]
    trivial
  exact Submodule.mem_map.mp hzmem

/-- If [a piecewise affine map is transverse to zero](hyp:hg), [a face is
in the complex](hyp:hs), and [its dimension is smaller than the target
dimension](hyp:hdim), and [a point belongs to that face](hyp:hx), [the map is
nonzero at that point](goal). -/
theorem PLMap.TransverseToZero.ne_zero_of_card [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {Q : Geometry.SimplicialComplex ℝ E} {g : PLMap Q F}
    (hg : g.TransverseToZero) {s : Finset E} (hs : s ∈ Q.faces)
    (hdim : s.card - 1 < Module.finrank ℝ F) (x : E)
    (hx : x ∈ convexHull ℝ (s : Set E)) :
    g ⟨x, Q.convexHull_subset_space hs hx⟩ ≠ 0 := by
  intro hz
  obtain ⟨a, _, hsurj⟩ := hg s hs x hx hz
  let D := (affineSpan ℝ (s : Set E)).direction
  have hsurj' : Function.Surjective (a.linear.comp D.subtype) := by
    intro z
    obtain ⟨v, hv, hvz⟩ := hsurj z
    exact ⟨⟨v, hv⟩, hvz⟩
  have hrank : Module.finrank ℝ F ≤ Module.finrank ℝ D :=
    LinearMap.finrank_le_finrank_of_surjective hsurj'
  have hdimD : Module.finrank ℝ D = s.card - 1 := by
    have hc : Fintype.card s = s.card - 1 + 1 := by
      rw [Fintype.card_coe]
      exact (Nat.sub_add_cancel (Q.nonempty_of_mem_faces hs).card_pos).symm
    have hr := (Q.indep hs).finrank_vectorSpan hc
    change Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction = s.card - 1
    rw [direction_affineSpan]
    have hrange : Set.range ((↑) : s → E) = (s : Set E) := by
      ext y
      simp
    rwa [hrange] at hr
  exact (hdimD ▸ hrank).not_gt hdim

/-- Given [a finite geometric complex](hyp:hQ), [a simplicial action of a
finite group](hyp:α) [free on the realization](hyp:hfree), [a linear
representation on the target](hyp:ρ), [a continuous equivariant function](hyp:hf,heq),
and [a positive tolerance](hyp:hε), [some iterated subdivision admits an
equivariant piecewise affine map transverse to zero within that tolerance
everywhere](goal). -/
theorem exists_equivariant_transverse_approximation [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [Finite G]
    {Q : Geometry.SimplicialComplex ℝ E} (hQ : Q.faces.Finite)
    (α : SimplicialAction G Q) (ρ : G →* (F ≃ₗ[ℝ] F)) (hfree : α.IsFree)
    {f : Q.space → F} (hf : Continuous f) (heq : Equivariant α ρ f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∃ g : PLMap (sdIterate Q k) F,
      Equivariant (α.iterate k) ρ g ∧ g.TransverseToZero ∧
        ∀ x : (sdIterate Q k).space, dist (g x) (f (originalPoint Q k x)) < ε := by
  -- Interpolate f on a subdivision fine enough for ε / 2, subdivide once more so
  -- that vertex orbits are separated on faces, perturb the vertex values
  -- equivariantly into general position by less than ε / 2, and interpolate.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (interpolate_eventually_close hQ hf (half_pos hε))
  let R := sdIterate Q (N + 1)
  let β := α.iterate (N + 1)
  let v : R.vertices → F := fun p =>
    f (originalPoint Q (N + 1) (vertexPoint R p))
  have hv : VertexEquivariant β ρ v := by
    intro a p
    have h := interpolate_equivariant α ρ heq (N + 1) a (vertexPoint R p)
    change PLMap.ofVertices R v (vertexPoint R (β.onVertices a p)) =
      ρ a (PLMap.ofVertices R v (vertexPoint R p)) at h
    simpa only [PLMap.ofVertices_vertex] using h
  obtain ⟨w, hweq, hwgp, hw⟩ := exists_equivariant_generalPosition
    (sdIterate_finite hQ (N + 1)) β ρ
    (SimplicialAction.iterate_free hfree (N + 1))
    (α.iterate N).subdivide_orbitSeparated hv (half_pos hε)
  refine ⟨N + 1, PLMap.ofVertices R w,
    PLMap.ofVertices_equivariant β ρ hweq, PLMap.ofVertices_transverse hwgp, ?_⟩
  intro x
  calc
    dist (PLMap.ofVertices R w x) (f (originalPoint Q (N + 1) x)) ≤
        dist (PLMap.ofVertices R w x) (interpolate Q f (N + 1) x) +
          dist (interpolate Q f (N + 1) x) (f (originalPoint Q (N + 1) x)) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add
      (PLMap.dist_ofVertices_lt hw x)
      (hN (N + 1) (Nat.le_succ N) x)
    _ = ε := add_halves ε

end Toolkit.Foundations.Topology
