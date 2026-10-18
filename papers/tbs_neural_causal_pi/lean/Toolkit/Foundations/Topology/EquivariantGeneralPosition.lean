module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.ExistsUnique
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real
public import Toolkit.Foundations.LinearAlgebra.AffineGeneralPosition
public import Toolkit.Foundations.Topology.BarycentricSubdivision
public import Toolkit.Foundations.Topology.SimplicialAction

/-!
# Equivariant vertex perturbation into general position relative to zero

Vertex values of a complex are in general position relative to zero
(`VertexGeneralPosition`) when on each face their affine span misses zero or is the whole
target. Under a free simplicial action of a finite group whose orbits meet each face at most
once (`SimplicialAction.OrbitSeparated`, which holds after one barycentric subdivision), any
equivariant vertex values can be moved by less than any tolerance to equivariant values in
general position (`exists_equivariant_generalPosition`; Matoušek, *Using the Borsuk–Ulam
Theorem*, §5.4). The values at orbit representatives are chosen one at a time by
`Toolkit.Foundations.LinearAlgebra.exists_generalPosition_coordinates`; closeness is
encoded through the inverse images of balls under the finitely many representation
operators, since the action need not preserve norms.
-/

@[expose] public section

namespace Toolkit.Foundations.Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Group G]

/-- For [a complex](hyp:Q) in [a real normed space](hyp:E) and [vertex
values](hyp:v) in [a target space](hyp:F), [general position relative to
zero](goal) means that on each face the affine span of the values either
misses zero or is the whole target space. -/
def VertexGeneralPosition (Q : Geometry.SimplicialComplex ℝ E) (v : Q.vertices → F) : Prop :=
  ∀ (s : Finset E), s ∈ Q.faces →
    0 ∈ affineSpan ℝ (v '' {p : Q.vertices | (p : E) ∈ s}) →
      affineSpan ℝ (v '' {p : Q.vertices | (p : E) ∈ s}) = ⊤

/-- A [simplicial action](hyp:α) of [a group](hyp:G) on [a complex](hyp:Q)
in [a real normed space](hyp:E) has [separated vertex orbits on faces](goal)
if two vertices in the same face that belong to the same orbit must coincide. -/
def SimplicialAction.OrbitSeparated {Q : Geometry.SimplicialComplex ℝ E}
    (α : SimplicialAction G Q) : Prop :=
  ∀ (s : Finset E), s ∈ Q.faces → ∀ u ∈ s, ∀ v ∈ s, ∀ g : G,
    α.action g u = v → u = v

/-- Any [simplicial action](hyp:α) [has separated vertex orbits after one
barycentric subdivision](goal). -/
theorem SimplicialAction.subdivide_orbitSeparated {Q : Geometry.SimplicialComplex ℝ E}
    (α : SimplicialAction G Q) : α.subdivide.OrbitSeparated := by
  intro s hs u hu v hv g h
  exact α.sd_orbit_separated hs hu hv g h

/-- For [a finite complex](hyp:hQ), [a free simplicial action](hyp:α,hfree)
with [separated vertex orbits on faces](hyp:hsep), [a linear
representation](hyp:ρ), [equivariant vertex values](hyp:hv), and [a positive
tolerance](hyp:hε), [there are equivariant vertex values in general position
within that tolerance at every vertex](goal). -/
theorem exists_equivariant_generalPosition [Finite G] [FiniteDimensional ℝ F]
    {Q : Geometry.SimplicialComplex ℝ E} (hQ : Q.faces.Finite)
    (α : SimplicialAction G Q) (ρ : G →* (F ≃ₗ[ℝ] F))
    (hfree : α.IsFree) (hsep : α.OrbitSeparated)
    {v : Q.vertices → F} (hv : VertexEquivariant α ρ v) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : Q.vertices → F, VertexEquivariant α ρ w ∧
      VertexGeneralPosition Q w ∧ ∀ p, dist (w p) (v p) < ε := by
  classical
  obtain ⟨R, hR⟩ := α.exists_vertex_orbit_coordinates hQ hfree
  choose c hc huniq using hR
  have hmul (g h : G) (p : Q.vertices) :
      α.onVertices (g * h) p = α.onVertices g (α.onVertices h p) := by
    apply Subtype.ext
    change α.action (g * h) p = α.action g (α.action h p)
    simp [Equiv.Perm.mul_apply]
  have hcoord (g : G) (p : Q.vertices) :
      c (α.onVertices g p) = ((c p).1, g * (c p).2) := by
    apply (huniq (α.onVertices g p) _ ?_).symm
    rw [hmul, hc]
  have hvfinite : Q.vertices.Finite := by
    rw [Q.vertices_eq]
    exact hQ.biUnion (fun s _ => s.finite_toSet)
  let : Finite Q.vertices := hvfinite.to_subtype
  let : Fintype Q.vertices := Fintype.ofFinite _
  let : Finite Q.faces := hQ.to_subtype
  let : Fintype R := Fintype.ofFinite _
  let V (j : Q.faces) : Set Q.vertices := {p | p.val ∈ j.val}
  let s (j : Q.faces) : Finset R := ((fun p => (c p).1) '' V j).toFinset
  have hsinj (j : Q.faces) (p q : Q.vertices) (hp : p ∈ V j) (hq : q ∈ V j)
      (he : (c p).1 = (c q).1) : p = q := by
    apply Subtype.ext
    apply hsep j.val j.property p.val hp q.val hq ((c q).2 * ((c p).2)⁻¹)
    change (α.onVertices ((c q).2 * ((c p).2)⁻¹) p).val = q.val
    have hh : α.onVertices ((c q).2 * ((c p).2)⁻¹) p = q := by
      calc
        α.onVertices ((c q).2 * ((c p).2)⁻¹) p =
            α.onVertices ((c q).2 * ((c p).2)⁻¹)
              (α.onVertices (c p).2 (c p).1) := congrArg _ (hc p).symm
        _ = α.onVertices (c q).2 (c p).1 := by
          rw [← hmul, inv_mul_cancel_right]
        _ = q := by rw [he, hc q]
    simpa using congrArg Subtype.val hh
  have hs (j : Q.faces) (r : R) : r ∈ s j ↔ ∃ p ∈ V j, (c p).1 = r := by
    simp [s]
  let pick (j : Q.faces) (r : R) (hr : r ∈ s j) : Q.vertices :=
    (hs j r |>.mp hr).choose
  have hpick (j : Q.faces) (r : R) (hr : r ∈ s j) :
      pick j r hr ∈ V j ∧ (c (pick j r hr)).1 = r :=
    (hs j r |>.mp hr).choose_spec
  let L (j : Q.faces) (r : R) : F ≃ₗ[ℝ] F :=
    if hr : r ∈ s j then ρ (c (pick j r hr)).2 else LinearEquiv.refl ℝ F
  let U (r : R) : Set F := ⋂ g : G, (ρ g) ⁻¹' Metric.ball (ρ g (v r)) ε
  have hU (r : R) : IsOpen (U r) := by
    apply isOpen_iInter_of_finite
    intro g
    exact Metric.isOpen_ball.preimage (ρ g).toLinearMap.continuous_of_finiteDimensional
  have hne (r : R) : (U r).Nonempty := by
    refine ⟨v r, Set.mem_iInter.mpr (fun g => ?_)⟩
    simpa using hε
  obtain ⟨z, hz, hgood⟩ := Toolkit.Foundations.LinearAlgebra.exists_generalPosition_coordinates
    Finset.univ s (fun _ _ _ => Finset.mem_univ _) L U
    (fun r _ => hU r) (fun r _ => hne r)
  let w (p : Q.vertices) : F := ρ (c p).2 (z (c p).1)
  have hvalue (j : Q.faces) (p : Q.vertices) (hp : p ∈ V j) :
      L j (c p).1 (z (c p).1) = w p := by
    have hr : (c p).1 ∈ s j := (hs j _).mpr ⟨p, hp, rfl⟩
    have he : pick j (c p).1 hr = p :=
      hsinj j _ _ (hpick j _ hr).1 hp (hpick j _ hr).2
    simp only [L, dif_pos hr, he, w]
  refine ⟨w, ?_, ?_, ?_⟩
  · intro g p
    simp only [w, hcoord, map_mul, LinearEquiv.mul_apply]
  · intro t ht
    let j : Q.faces := ⟨t, ht⟩
    have himage : w '' {p : Q.vertices | p.val ∈ t} =
        (fun r => L j r (z r)) '' (s j : Set R) := by
      apply Set.ext
      intro y
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨(c p).1, (hs j _).mpr ⟨p, hp, rfl⟩, hvalue j p hp⟩
      · rintro ⟨r, hr, rfl⟩
        obtain ⟨p, hp, he⟩ := (hs j r).mp hr
        refine ⟨p, hp, ?_⟩
        rw [← he]
        exact (hvalue j p hp).symm
    rw [himage]
    exact hgood j
  · intro p
    have hp := Set.mem_iInter.mp (hz (c p).1 (Finset.mem_univ _)) (c p).2
    have he : v p = ρ (c p).2 (v (c p).1) := by
      rw [← hv, hc]
    simpa only [w, he, Set.mem_preimage, Metric.mem_ball] using hp

end Toolkit.Foundations.Topology
