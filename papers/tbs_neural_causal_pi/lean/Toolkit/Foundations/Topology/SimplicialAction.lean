module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.AffineSpace.Centroid
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.ExistsUnique
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.Closure
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Toolkit.Foundations.Topology.BarycentricSubdivision
public import Toolkit.Foundations.Topology.PiecewiseAffine

/-!
# Simplicial group actions and equivariant interpolation

A simplicial action (`SimplicialAction`) of a group on a geometric simplicial complex is a
homomorphism into permutations of the ambient space that maps faces to faces and is affine
on each face (it need not be affine on the whole space; an action on a realization extends
by the identity off it). This module provides:

* the induced actions on the underlying space and on vertices, freeness (`IsFree`, on all
  points of the realization), and equivariance of maps and of vertex assignments;
* `PLMap.ofVertices_equivariant`: an equivariant vertex assignment interpolates to an
  equivariant piecewise affine map;
* naturality of barycentric subdivision: `SimplicialAction.subdivide` acts on `sd Q`, and
  `SimplicialAction.sd_orbit_separated` (two vertices of one face of `sd Q` in the same
  orbit coincide);
* `SimplicialAction.exists_vertex_orbit_coordinates`: under a free action on a finite
  complex, every vertex is uniquely a group element applied to one of finitely many orbit
  representatives (Mathlib's `MulAction.selfEquivOrbitsQuotientProd`).
-/

@[expose] public section

namespace Toolkit.Foundations.Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Group G]

open Classical in
/-- A [simplicial action](goal) of [a group](hyp:G) on [a complex](hyp:Q)
in [a real normed space](hyp:E)
consists of [permutations obeying the group law](step:1) that [preserve
faces](step:2) and [are affine on every face](step:3). -/
structure SimplicialAction (G : Type*) [Group G] (Q : Geometry.SimplicialComplex ℝ E) where
  /-- A [simplicial action](hyp:self) of [a group](hyp:G) on [a complex](hyp:Q)
  in [a real normed space](hyp:E) supplies [permutations of the ambient space
  respecting multiplication and the identity](goal). -/
  action : G →* Equiv.Perm E
  /-- Under [a simplicial action](hyp:self), applying [a group element](hyp:g)
  to [a finite vertex set](hyp:s) that [is a face](hyp:_hs)
  [gives another face](goal). -/
  face_image : ∀ (g : G) (s : Finset E) (_hs : s ∈ Q.faces),
    s.image (action g) ∈ Q.faces
  /-- Under [a simplicial action](hyp:self), for [a group element](hyp:g)
  and [a finite vertex set](hyp:s) that [is a face](hyp:_hs), [there is an
  ambient affine map agreeing with the action at every point of its convex
  hull](goal). -/
  affine_on_face : ∀ (g : G) (s : Finset E) (_hs : s ∈ Q.faces), ∃ a : E →ᵃ[ℝ] E,
    ∀ x ∈ convexHull ℝ (s : Set E), action g x = a x

open Classical in
/-- Under [a simplicial action](hyp:α), [a face of the complex](hyp:hs)
and [a point in its convex hull](hyp:hx) [are sent to a point in the convex
hull of the image face](goal). -/
theorem SimplicialAction.maps_convexHull {Q : Geometry.SimplicialComplex ℝ E}
    (α : SimplicialAction G Q) (g : G) {s : Finset E} (hs : s ∈ Q.faces)
    {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) :
    α.action g x ∈ convexHull ℝ (s.image (α.action g) : Set E) := by
  obtain ⟨a, ha⟩ := α.affine_on_face g s hs
  rw [ha x hx]
  have himage : a '' (s : Set E) = (s.image (α.action g) : Set E) := by
    rw [Finset.coe_image]
    apply Set.image_congr
    intro y hy
    exact (ha y (subset_convexHull ℝ _ hy)).symm
  rw [← himage, ← a.image_convexHull]
  exact ⟨x, hx, rfl⟩

/-- Under [a simplicial action](hyp:α), [the image of a point in the
realization](hyp:hx) [remains in the realization](goal). -/
theorem SimplicialAction.maps_space {Q : Geometry.SimplicialComplex ℝ E}
    (α : SimplicialAction G Q) (g : G) {x : E} (hx : x ∈ Q.space) :
    α.action g x ∈ Q.space := by
  obtain ⟨s, hs, hxs⟩ := Q.mem_space_iff.mp hx
  exact Q.convexHull_subset_space (α.face_image g s hs) (α.maps_convexHull g hs hxs)

/-- For [a complex](hyp:Q) in [a real normed space](hyp:E), the [action on
the realization](goal) induced by [a simplicial action](hyp:α) of [a group](hyp:G)
applies [a group element](hyp:g) to [a point](hyp:x). -/
def SimplicialAction.onSpace {Q : Geometry.SimplicialComplex ℝ E}
    (α : SimplicialAction G Q) (g : G) (x : Q.space) : Q.space :=
  ⟨α.action g x, α.maps_space g x.property⟩

/-- For [a complex](hyp:Q) in [a real normed space](hyp:E), the [action on
vertices](goal) induced by [a simplicial action](hyp:α) of [a group](hyp:G)
applies [a group element](hyp:g) to [a vertex](hyp:v). -/
noncomputable def SimplicialAction.onVertices {Q : Geometry.SimplicialComplex ℝ E}
    (α : SimplicialAction G Q) (g : G) (v : Q.vertices) : Q.vertices := by
  classical
  refine ⟨α.action g v, ?_⟩
  simpa [Geometry.SimplicialComplex.vertices] using α.face_image g {v.val} v.property

/-- A [simplicial action](hyp:α) of [a group](hyp:G) on [a complex](hyp:Q)
in [a real normed space](hyp:E) is [free on the realization](goal) when only
the identity group element fixes any point. -/
def SimplicialAction.IsFree {Q : Geometry.SimplicialComplex ℝ E}
    (α : SimplicialAction G Q) : Prop :=
  ∀ (g : G) (x : Q.space), α.onSpace g x = x → g = 1

/-- For [a simplicial action](hyp:α) of [a group](hyp:G) on [a complex](hyp:Q)
in [a real normed space](hyp:E) and [a linear representation](hyp:ρ) on
[a target space](hyp:F), [equivariance](goal) means that [a function](hyp:f)
commutes with these actions at every point of the realization. -/
def Equivariant {Q : Geometry.SimplicialComplex ℝ E} (α : SimplicialAction G Q)
    (ρ : G →* (F ≃ₗ[ℝ] F)) (f : Q.space → F) : Prop :=
  ∀ g x, f (α.onSpace g x) = ρ g (f x)

/-- For [a simplicial action](hyp:α) of [a group](hyp:G) on [a complex](hyp:Q)
in [a real normed space](hyp:E), [a linear representation](hyp:ρ) on
[a target space](hyp:F), and [vertex values](hyp:v), [vertex equivariance](goal)
means that the assignment commutes with the group actions at every vertex. -/
def VertexEquivariant {Q : Geometry.SimplicialComplex ℝ E} (α : SimplicialAction G Q)
    (ρ : G →* (F ≃ₗ[ℝ] F)) (v : Q.vertices → F) : Prop :=
  ∀ g p, v (α.onVertices g p) = ρ g (v p)

/-- If [a vertex assignment is equivariant](hyp:hv) for [a simplicial
action](hyp:α) and [a linear representation](hyp:ρ), [its interpolant is
equivariant on the entire realization](goal). -/
theorem PLMap.ofVertices_equivariant [FiniteDimensional ℝ E]
    {Q : Geometry.SimplicialComplex ℝ E} (α : SimplicialAction G Q)
    (ρ : G →* (F ≃ₗ[ℝ] F)) {v : Q.vertices → F} (hv : VertexEquivariant α ρ v) :
    Equivariant α ρ (PLMap.ofVertices Q v) := by
  classical
  intro g x
  let f := PLMap.ofVertices Q v
  let l : PLMap Q F :=
    { toFun := fun y => f (α.onSpace g y)
      affine_on_face := by
        intro s hs
        obtain ⟨a, ha⟩ := α.affine_on_face g s hs
        obtain ⟨b, hb⟩ := f.affine_on_face (s.image (α.action g)) (α.face_image g s hs)
        refine ⟨b.comp a, ?_⟩
        intro y hy
        change f (α.onSpace g ⟨y, _⟩) = b (a y)
        rw [← ha y hy]
        exact hb (α.action g y) (α.maps_convexHull g hs hy) }
  let r : PLMap Q F :=
    { toFun := fun y => ρ g (f y)
      affine_on_face := by
        intro s hs
        obtain ⟨a, ha⟩ := f.affine_on_face s hs
        refine ⟨(ρ g).toLinearMap.toAffineMap.comp a, ?_⟩
        intro y hy
        change ρ g (f ⟨y, _⟩) = ρ g (a y)
        rw [ha y hy] }
  have heq : l = r := PLMap.ext_vertices (fun p => by
    change f (vertexPoint Q (α.onVertices g p)) = ρ g (f (vertexPoint Q p))
    rw [PLMap.ofVertices_vertex, PLMap.ofVertices_vertex]
    exact hv g p)
  exact congrArg (fun m : PLMap Q F => m x) heq

open Classical in
/-- Under [a simplicial action](hyp:α), [the barycenter of a face](hyp:hs)
[is sent to the barycenter of the image face](goal). -/
theorem SimplicialAction.map_barycenter {Q : Geometry.SimplicialComplex ℝ E}
    (α : SimplicialAction G Q) (g : G) {s : Finset E} (hs : s ∈ Q.faces) :
    α.action g (barycenter s) = barycenter (s.image (α.action g)) := by
  obtain ⟨a, ha⟩ := α.affine_on_face g s hs
  have hn := Q.nonempty_of_mem_faces hs
  have hc (t : Finset E) (ht : t.Nonempty) : t.centroid ℝ id = barycenter t := by
    rw [Finset.centroid_eq_centerMass t ht]
    have hcard : (t.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ht)
    simpa [Finset.centroidWeights, Pi.smul_def, smul_eq_mul,
      Function.const_def, barycenter]
      using (t.centerMass_smul_left (w := fun _ => (1 : ℝ)) (z := id)
        (inv_ne_zero hcard))
  rw [ha _ (barycenter_mem_convexHull hn), ← hc s hn,
    ← hc _ (hn.image (α.action g))]
  rw [Finset.centroid_def, Finset.map_affineCombination _ _ _
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hn)]
  change s.centroid ℝ (a ∘ id) = _
  calc
    s.centroid ℝ (a ∘ id) = s.centroid ℝ (α.action g) := by
      apply Finset.affineCombination_congr
      · intro i hi; rfl
      · intro i hi
        exact (ha i (subset_convexHull ℝ _ hi)).symm
    _ = (s.image (α.action g)).centroid ℝ id := by
      apply Finset.centroid_eq_of_inj_on_of_image_eq
      · intro i hi j hj hij; exact (α.action g).injective hij
      · intro i hi j hj hij; exact hij
      · simp

open Classical in
/-- Under [a simplicial action](hyp:α), [a face of the barycentric
subdivision](hyp:hs) [is sent to another face of that subdivision](goal). -/
theorem SimplicialAction.sd_face_image {Q : Geometry.SimplicialComplex ℝ E}
    (α : SimplicialAction G Q) (g : G) {s : Finset E} (hs : s ∈ (sd Q).faces) :
    s.image (α.action g) ∈ (sd Q).faces := by
  obtain ⟨C, hC, rfl⟩ := hs
  refine ⟨C.image (fun t => t.image (α.action g)), ?_, ?_⟩
  · refine ⟨hC.1.image _, ?_, ?_⟩
    · intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      exact α.face_image g u (hC.2.1 u hu)
    · intro t ht u hu
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hu
      exact (hC.2.2 A hA B hB).imp Finset.image_subset_image Finset.image_subset_image
  · simp only [Finset.image_image]
    apply Finset.image_congr
    intro t ht
    exact α.map_barycenter g (hC.2.1 t ht)

/-- For [a simplicial action](hyp:α) of [a group](hyp:G) on [a complex](hyp:Q)
in [a real normed space](hyp:E), the [subdivided action](goal) retains
[the same point permutations](step:1), [their preservation of subdivision
faces](step:2), and [their affine extensions on each subdivision face](step:3). -/
noncomputable def SimplicialAction.subdivide {Q : Geometry.SimplicialComplex ℝ E}
    (α : SimplicialAction G Q) : SimplicialAction G (sd Q) where
  action := α.action
  face_image := fun g _ hs => α.sd_face_image g hs
  affine_on_face := by
    intro g s hs
    obtain ⟨t, ht, hst⟩ := sd_face_subset hs
    obtain ⟨a, ha⟩ := α.affine_on_face g t ht
    exact ⟨a, fun x hx => ha x (hst hx)⟩

/-- In [a simplex of the subdivision](hyp:hs), [two vertices](hyp:hu,hv)
that [are related by a group element under a simplicial action](hyp:h)
[are equal](goal). -/
theorem SimplicialAction.sd_orbit_separated {Q : Geometry.SimplicialComplex ℝ E}
    (α : SimplicialAction G Q) {s : Finset E} (hs : s ∈ (sd Q).faces)
    {u v : E} (hu : u ∈ s) (hv : v ∈ s) (g : G) (h : α.action g u = v) : u = v := by
  classical
  obtain ⟨C, hC, rfl⟩ := hs
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hv
  have hAB : A.image (α.action g) = B :=
    barycenter_injective_on_faces (α.face_image g A (hC.2.1 A hA))
      (hC.2.1 B hB) ((α.map_barycenter g (hC.2.1 A hA)).symm.trans h)
  have hcard : A.card = B.card := by
    rw [← hAB, Finset.card_image_of_injective _ (α.action g).injective]
  have heq : A = B := by
    rcases hC.2.2 A hA B hB with hab | hba
    · exact Finset.eq_of_subset_of_card_le hab hcard.ge
    · exact (Finset.eq_of_subset_of_card_le hba hcard.le).symm
  rw [heq]

/-- For [a complex with finitely many faces](hyp:hQ) and [a simplicial
action](hyp:α) [free on its realization](hyp:hfree), [there is a finite set
of representative vertices such that every vertex has a unique expression
as a group element applied to one representative](goal). -/
theorem SimplicialAction.exists_vertex_orbit_coordinates
    {Q : Geometry.SimplicialComplex ℝ E} (hQ : Q.faces.Finite)
    (α : SimplicialAction G Q) (hfree : α.IsFree) :
    ∃ R : Finset Q.vertices, ∀ p : Q.vertices,
      ∃! rg : R × G, α.onVertices rg.2 rg.1 = p := by
  classical
  let : MulAction G Q.vertices :=
    { smul := α.onVertices
      one_smul := fun p => Subtype.ext (by
        change α.action 1 p = p
        simp)
      mul_smul := fun g h p => Subtype.ext (by
        change α.action (g * h) p = α.action g (α.action h p)
        simp [Equiv.Perm.mul_apply]) }
  have hstab (p : Q.vertices) : MulAction.stabilizer G p = ⊥ := by
    apply le_antisymm _ bot_le
    intro g hg
    apply Subgroup.mem_bot.mpr
    apply hfree g (vertexPoint Q p)
    apply Subtype.ext
    change α.action g p = p
    exact congrArg (Subtype.val : Q.vertices → E) (MulAction.mem_stabilizer_iff.mp hg)
  have hv : Q.vertices.Finite := by
    rw [Q.vertices_eq]
    exact hQ.biUnion (fun s _ => s.finite_toSet)
  let : Finite Q.vertices := hv.to_subtype
  let := Fintype.ofFinite Q.vertices
  let Ω := Quotient (MulAction.orbitRel G Q.vertices)
  let e : Q.vertices ≃ Ω × G := MulAction.selfEquivOrbitsQuotientProd hstab
  have he (q : Ω) (g : G) : e.symm (q, g) = α.onVertices g q.out := by
    rfl
  let R : Finset Q.vertices := (Set.range (Quotient.out : Ω → Q.vertices)).toFinset
  refine ⟨R, fun p => ?_⟩
  have hmem (q : Ω) : q.out ∈ R := by
    exact Set.mem_toFinset.mpr ⟨q, rfl⟩
  refine ⟨(⟨(e p).1.out, hmem (e p).1⟩, (e p).2), ?_, ?_⟩
  · change α.onVertices (e p).2 (e p).1.out = p
    rw [← he]
    exact e.symm_apply_apply p
  · intro rg hrg
    obtain ⟨q, hq⟩ := Set.mem_toFinset.mp rg.1.property
    have hpair : (q, rg.2) = e p := by
      apply e.symm.injective
      rw [he, hq, hrg, e.symm_apply_apply]
    apply Prod.ext
    · apply Subtype.ext
      exact hq.symm.trans (congrArg (fun z : Ω × G => z.1.out) hpair)
    · exact congrArg (fun z : Ω × G => z.2) hpair

end Toolkit.Foundations.Topology
