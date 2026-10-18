module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.AffineSpace.Centroid
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.Closure
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Toolkit.Foundations.Topology.ChainVertexWeights

/-!
# Geometric barycentric subdivision

For a geometric simplicial complex `Q` (Mathlib's `Geometry.SimplicialComplex ℝ E`), the
barycentric subdivision `sd Q` is the complex whose faces are the sets of barycenters of
chains of faces of `Q` (Matoušek, *Using the Borsuk–Ulam Theorem*, Definition 1.7.2;
Munkres, *Elements of Algebraic Topology*, §15). This module provides:

* `barycenter`, `barycenter_mem_convexHull`, `barycenter_injective_on_faces`;
* `IsFaceChain`, `barycentricFaces` and the three complex axioms for them
  (`barycentricFaces_independent`, `barycentricFaces_down_closed`, `barycentricFaces_inter`);
* the complex `sd Q`, with `sd_vertices` (its vertices are the barycenters of faces),
  `sd_face_subset` (each new face lies in an old face), `sd_space` (same underlying space)
  and `sd_finite`.

Coverage sorts barycentric coordinates: the level sets of a point's coordinates form a
chain and their differences give the chain weights (`exists_chainVertexWeight`).
-/

@[expose] public section

namespace Toolkit.Foundations.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The [barycenter](goal) of [a finite collection of points](hyp:s) in
[a real normed space](hyp:E) is their equally weighted center of mass, with
zero used for the empty collection. -/
noncomputable def barycenter (s : Finset E) : E :=
  s.centerMass (fun _ => (1 : ℝ)) id

/-- If [a finite collection of points is nonempty](hyp:hs), its [barycenter lies
in its convex hull](goal). -/
theorem barycenter_mem_convexHull {s : Finset E} (hs : s.Nonempty) :
    barycenter s ∈ convexHull ℝ (s : Set E) := by
  apply Finset.centerMass_id_mem_convexHull
  · intro i hi
    exact zero_le_one
  · simpa using (Nat.cast_pos (α := ℝ)).mpr (Finset.card_pos.mpr hs)

/-- For [a geometric complex](hyp:Q) in [a real normed space](hyp:E),
[a finite family of vertex sets](hyp:C)
is a [face chain](goal) when it
[is nonempty](step:1), [consists of faces of the complex](step:2), and
[has every pair comparable by inclusion](step:3). -/
def IsFaceChain (Q : Geometry.SimplicialComplex ℝ E) (C : Finset (Finset E)) : Prop :=
  C.Nonempty ∧ (∀ s ∈ C, s ∈ Q.faces) ∧
    ∀ s ∈ C, ∀ t ∈ C, s ⊆ t ∨ t ⊆ s

/-- For [a geometric complex](hyp:Q) in [a real normed space](hyp:E), its
[barycentric faces](goal) are the finite sets for which there is
[a chain of original faces](step:1) whose [set of barycenters equals that
finite set](step:2). -/
noncomputable def barycentricFaces (Q : Geometry.SimplicialComplex ℝ E) : Set (Finset E) :=
  by
    classical
    exact {t | ∃ C : Finset (Finset E), IsFaceChain Q C ∧ t = C.image barycenter}

/-- If [a nonempty finite vertex set](hyp:hs) [is affinely independent](hyp:hi),
and [a subset](hyp:ht) [omits at least one vertex](hyp:hne), [the barycenter
of the full set lies outside the affine span of that subset](goal). -/
theorem barycenter_notMem_affineSpan {s t : Finset E}
    (hs : s.Nonempty) (hi : AffineIndependent ℝ ((↑) : s → E))
    (ht : t ⊆ s) (hne : ¬ s ⊆ t) :
    barycenter s ∉ affineSpan ℝ (t : Set E) := by
  classical
  intro hm
  obtain ⟨x, hxs, hxt⟩ := Finset.not_subset.mp hne
  have he : Finset.univ.affineCombination ℝ ((↑) : s → E)
      (Finset.univ.centroidWeights ℝ) = barycenter s := by
    rw [← Finset.centroid_def, Finset.centroid_univ,
      Finset.centroid_eq_centerMass s hs]
    have hn : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs)
    simp [barycenter, Finset.centerMass, Finset.centroidWeights, hn,
      Finset.smul_sum]
  have himage : ((↑) : s → E) '' {i : s | (i : E) ∈ t} = (t : Set E) := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hy
      exact ⟨⟨y, ht hy⟩, hy, rfl⟩
  have hw := hi.eq_zero_of_affineCombination_mem_affineSpan
    (Finset.univ.sum_centroidWeights_eq_one_of_nonempty ℝ
      (by simpa using hs))
    (s := {i : s | (i : E) ∈ t})
    (by rw [he, himage]; exact hm) (i := ⟨x, hxs⟩) (Finset.mem_univ _) hxt
  have hn : (Fintype.card s : ℝ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs) : (s.card : ℝ) ≠ 0)
  exact (inv_ne_zero hn) (by simpa [Finset.centroidWeights] using hw)

/-- If [two collections are faces of the same complex](hyp:hs,ht) and [their
barycenters coincide](hyp:h), then [the collections are equal](goal). -/
theorem barycenter_injective_on_faces {Q : Geometry.SimplicialComplex ℝ E}
    {s t : Finset E} (hs : s ∈ Q.faces) (ht : t ∈ Q.faces)
    (h : barycenter s = barycenter t) : s = t := by
  -- Gluing puts the common barycenter in the hull of s ∩ t. Positivity and
  -- uniqueness of the barycentric coordinates of s and of t force s = t.
  classical
  have hm : barycenter s ∈ convexHull ℝ (s ∩ t : Set E) :=
    Q.inter_subset_convexHull hs ht ⟨barycenter_mem_convexHull
      (Q.nonempty_of_mem_faces hs), h ▸ barycenter_mem_convexHull
      (Q.nonempty_of_mem_faces ht)⟩
  have hms : barycenter s ∈ affineSpan ℝ (s ∩ t : Set E) :=
    convexHull_subset_affineSpan (𝕜 := ℝ) (s ∩ t : Set E) hm
  have hmt : barycenter t ∈ affineSpan ℝ (s ∩ t : Set E) := h ▸ hms
  apply Finset.Subset.antisymm
  · by_contra hn
    apply barycenter_notMem_affineSpan (Q.nonempty_of_mem_faces hs) (Q.indep hs)
      Finset.inter_subset_left (fun hi => hn (Finset.inter_subset_right.trans' hi))
    simpa only [Finset.coe_inter] using hms
  · by_contra hn
    apply barycenter_notMem_affineSpan (Q.nonempty_of_mem_faces ht) (Q.indep ht)
      Finset.inter_subset_right (fun hi => hn (Finset.inter_subset_left.trans' hi))
    simpa only [Finset.coe_inter] using hmt

/-- The barycenters in [a face chain](hyp:hC) are [affinely independent](goal). -/
theorem faceChain_affineIndependent {Q : Geometry.SimplicialComplex ℝ E}
    {C : Finset (Finset E)} (hC : IsFaceChain Q C) :
    AffineIndependent ℝ (fun s : C => barycenter (s : Finset E)) := by
  -- Remove the largest face. The remaining barycenters lie in the span of
  -- its largest proper predecessor, whereas its own barycenter does not.
  classical
  have main : ∀ D : Finset (Finset E),
      (∀ s ∈ D, s ∈ Q.faces) →
      (∀ s ∈ D, ∀ t ∈ D, s ⊆ t ∨ t ⊆ s) →
      AffineIndependent ℝ (fun s : D => barycenter (s : Finset E)) := by
    intro D
    induction D using Finset.strongInductionOn with
    | _ D ih =>
      intro hfaces hchain
      by_cases hempty : D = ∅
      · subst D
        exact affineIndependent_of_subsingleton ℝ _
      obtain ⟨s, hs, hmax⟩ := D.exists_max_image Finset.card
        (Finset.nonempty_iff_ne_empty.mpr hempty)
      have hsub : ∀ u ∈ D, u ⊆ s := by
        intro u hu
        rcases hchain u hu s hs with h | h
        · exact h
        · exact (Finset.eq_of_subset_of_card_le h (hmax u hu)).symm.subset
      have hrest := ih (D.erase s) (Finset.erase_ssubset hs)
        (fun u hu => hfaces u (Finset.mem_of_mem_erase hu))
        (fun u hu v hv => hchain u (Finset.mem_of_mem_erase hu)
          v (Finset.mem_of_mem_erase hv))
      let e : {u : D // u ≠ ⟨s, hs⟩} ↪ (D.erase s) :=
        ⟨fun u => ⟨u.1.1, Finset.mem_erase.mpr
          ⟨fun he => u.2 (Subtype.ext he), u.1.2⟩⟩,
          by
            intro a b he
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun v : D.erase s => (v : Finset E)) he⟩
      have hrest' : AffineIndependent ℝ
          (fun u : {u : D // u ≠ ⟨s, hs⟩} => barycenter (u.1 : Finset E)) :=
        hrest.comp_embedding e
      apply hrest'.affineIndependent_of_notMem_span
      by_cases hne : (D.erase s).Nonempty
      · obtain ⟨t, ht, htmax⟩ := (D.erase s).exists_max_image Finset.card hne
        have htD := Finset.mem_of_mem_erase ht
        have htproper : ¬ s ⊆ t := by
          intro h
          exact (Finset.mem_erase.mp ht).1 (Finset.Subset.antisymm h (hsub t htD)).symm
        have hspan : affineSpan ℝ
            ((fun u : D => barycenter (u : Finset E)) '' {u | u ≠ ⟨s, hs⟩}) ≤
            affineSpan ℝ (t : Set E) := by
          apply affineSpan_le.mpr
          rintro _ ⟨u, hu, rfl⟩
          have hu' : (u : Finset E) ∈ D.erase s :=
            Finset.mem_erase.mpr ⟨fun he => hu (Subtype.ext he), u.2⟩
          have hut : (u : Finset E) ⊆ t := by
            rcases hchain u u.2 t htD with h | h
            · exact h
            · exact (Finset.eq_of_subset_of_card_le h (htmax u hu')).symm.subset
          exact convexHull_subset_affineSpan (𝕜 := ℝ) (t : Set E)
            (convexHull_mono hut (barycenter_mem_convexHull
              (Q.nonempty_of_mem_faces (hfaces u u.2))))
        exact fun hm => barycenter_notMem_affineSpan
          (Q.nonempty_of_mem_faces (hfaces s hs)) (Q.indep (hfaces s hs))
          (hsub t htD) htproper (hspan hm)
      · have hr : {u : D | u ≠ ⟨s, hs⟩} = (∅ : Set D) := by
          ext u
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
          apply Subtype.ext
          by_contra hu
          exact hne ⟨u, Finset.mem_erase.mpr ⟨hu, u.2⟩⟩
        simpa [hr] using (AffineSubspace.notMem_bot ℝ E (barycenter s))
  exact main C hC.2.1 hC.2.2

/-- If [a finite set is a barycentric face](hyp:ht), then [its vertices are
affinely independent](goal). -/
theorem barycentricFaces_independent {Q : Geometry.SimplicialComplex ℝ E}
    {t : Finset E} (ht : t ∈ barycentricFaces Q) :
    AffineIndependent ℝ ((↑) : t → E) := by
  classical
  obtain ⟨C, hC, rfl⟩ := ht
  have hi := (faceChain_affineIndependent hC).range
  have hr : Set.range (fun s : C => barycenter (s : Finset E)) =
      (C.image barycenter : Set E) := by
    ext x
    simp
  rw [hr] at hi
  exact hi

/-- The [barycentric faces of a complex](hyp:Q) [are nonempty and closed under
taking nonempty subsets](goal). -/
theorem barycentricFaces_down_closed (Q : Geometry.SimplicialComplex ℝ E) :
    IsRelLowerSet (barycentricFaces Q) Finset.Nonempty := by
  classical
  rintro t ⟨C, hC, rfl⟩
  refine ⟨hC.1.image barycenter, ?_⟩
  intro u hu hune
  let D := C.filter (fun s => barycenter s ∈ u)
  have hDC : D ⊆ C := Finset.filter_subset _ _
  have hDne : D.Nonempty := by
    obtain ⟨x, hxu⟩ := hune
    obtain ⟨s, hsC, rfl⟩ := Finset.mem_image.mp (hu hxu)
    exact ⟨s, Finset.mem_filter.mpr ⟨hsC, hxu⟩⟩
  refine ⟨D, ⟨hDne, fun s hs => hC.2.1 s (hDC hs),
    fun s hs t ht => hC.2.2 s (hDC hs) t (hDC ht)⟩, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨s, hsC, rfl⟩ := Finset.mem_image.mp (hu hx)
    exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨hsC, hx⟩, rfl⟩
  · rintro hx
    obtain ⟨s, hsD, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hsD).2

open Classical in
/-- If [all sets in a finite family lie in a common finite vertex
set](hyp:hsub), [a weighted sum of their barycenters equals the sum of the
vertices weighted by their distributed coordinates](goal). -/
theorem sum_smul_barycenter_eq_chainVertexWeight {C : Finset (Finset E)}
    {U : Finset E} (hsub : ∀ s ∈ C, s ⊆ U) (w : Finset E → ℝ) :
    ∑ s ∈ C, w s • barycenter s =
      ∑ v ∈ U, chainVertexWeight C w v • v := by
  -- Expand centerMass, distribute scalar multiplication, and swap the sums.
  -- Restricting the U-sum to s is justified by hsub; no independence is used.
  classical
  simp only [chainVertexWeight, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [barycenter, Finset.centerMass, Finset.sum_const, nsmul_eq_mul,
    mul_one, one_smul, smul_smul, Finset.smul_sum, div_eq_mul_inv]
  rw [← Finset.sum_subset (hsub s hs)]
  · apply Finset.sum_congr rfl
    intro v hv
    simp [hv]
  · intro v hvU hvs
    simp [hvs]

/-- For [a face chain](hyp:hC) with [strictly positive weights](hyp:hw)
[summing to one](hyp:hsw), if [another face belongs to the complex](hyp:hs)
and [contains the weighted barycenter in its convex hull](hyp:hx), [every
member of the chain is contained in that face](goal). -/
theorem faceChain_weighted_sum_carrier {Q : Geometry.SimplicialComplex ℝ E}
    {C : Finset (Finset E)} (hC : IsFaceChain Q C) {w : Finset E → ℝ}
    (hw : ∀ t ∈ C, 0 < w t) (hsw : ∑ t ∈ C, w t = 1)
    {s : Finset E} (hs : s ∈ Q.faces)
    (hx : (∑ t ∈ C, w t • barycenter t) ∈ convexHull ℝ (s : Set E)) :
    ∀ t ∈ C, t ⊆ s := by
  -- Expand the point in the chain's largest face T; every vertex of T has a
  -- positive coefficient, and the intersection axiom places the point in
  -- hull(T ∩ s), so affine independence forces T ⊆ s.
  classical
  obtain ⟨T, hTC, hmax⟩ := C.exists_max_image Finset.card hC.1
  have hCT : ∀ t ∈ C, t ⊆ T := by
    intro t ht
    rcases hC.2.2 t ht T hTC with h | h
    · exact h
    · exact (Finset.eq_of_subset_of_card_le h (hmax t ht)).symm.subset
  have hT := hC.2.1 T hTC
  have hxT : (∑ t ∈ C, w t • barycenter t) ∈ convexHull ℝ (T : Set E) :=
    (convex_convexHull ℝ _).sum_mem (fun t ht => (hw t ht).le) hsw
      (fun t ht => convexHull_mono (hCT t ht)
        (barycenter_mem_convexHull (Q.nonempty_of_mem_faces (hC.2.1 t ht))))
  have hm := Q.inter_subset_convexHull hT hs ⟨hxT, hx⟩
  have hnorm : ∑ v : T, chainVertexWeight C w v = 1 := by
    simpa only [Finset.sum_coe_sort] using
      (sum_chainVertexWeight (fun t ht => Q.nonempty_of_mem_faces (hC.2.1 t ht))
        hCT w).trans hsw
  have he : Finset.univ.affineCombination ℝ ((↑) : T → E)
      (fun v => chainVertexWeight C w v) = ∑ t ∈ C, w t • barycenter t := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hnorm]
    rw [Finset.sum_coe_sort T (fun v => chainVertexWeight C w v • v)]
    exact (sum_smul_barycenter_eq_chainVertexWeight hCT w).symm
  have himage : ((↑) : T → E) '' {v : T | (v : E) ∈ s} = (T ∩ s : Set E) := by
    ext v
    simp [and_comm]
  have hTs : T ⊆ s := by
    intro v hv
    by_contra hvs
    have hz := (Q.indep hT).eq_zero_of_affineCombination_mem_affineSpan hnorm
      (s := {v : T | (v : E) ∈ s})
      (by rw [he, himage]; exact convexHull_subset_affineSpan (𝕜 := ℝ) _ hm)
      (i := ⟨v, hv⟩) (Finset.mem_univ _) hvs
    have hp := (chainVertexWeight_pos_iff hw v).mpr
      (Finset.mem_biUnion.mpr ⟨T, hTC, hv⟩)
    exact (ne_of_gt hp) hz
  exact fun t ht => (hCT t ht).trans hTs

open Classical in
/-- For [two face chains](hyp:hC,hD) [contained in one simplex](hyp:hs,hCs,hDs),
weights [summing to one on each chain](hyp:hsw,hsz) that [give the same
weighted barycenter](hyp:heq) [give the same distributed coordinate at every
vertex of that simplex](goal). -/
theorem faceChain_coordinates_eq {Q : Geometry.SimplicialComplex ℝ E}
    {C D : Finset (Finset E)} (hC : IsFaceChain Q C) (hD : IsFaceChain Q D)
    {s : Finset E} (hs : s ∈ Q.faces)
    (hCs : ∀ t ∈ C, t ⊆ s) (hDs : ∀ t ∈ D, t ⊆ s)
    {w z : Finset E → ℝ}
    (hsw : ∑ t ∈ C, w t = 1) (hsz : ∑ t ∈ D, z t = 1)
    (heq : ∑ t ∈ C, w t • barycenter t = ∑ t ∈ D, z t • barycenter t) :
    ∀ v ∈ s, chainVertexWeight C w v = chainVertexWeight D z v := by
  classical
  have hwone : ∑ v : s, chainVertexWeight C w v = 1 := by
    simpa only [Finset.sum_coe_sort] using
      (sum_chainVertexWeight (fun t ht => Q.nonempty_of_mem_faces (hC.2.1 t ht))
        hCs w).trans hsw
  have hzone : ∑ v : s, chainVertexWeight D z v = 1 := by
    simpa only [Finset.sum_coe_sort] using
      (sum_chainVertexWeight (fun t ht => Q.nonempty_of_mem_faces (hD.2.1 t ht))
        hDs z).trans hsz
  have he : Finset.univ.affineCombination ℝ ((↑) : s → E)
      (fun v => chainVertexWeight C w v) =
      Finset.univ.affineCombination ℝ ((↑) : s → E)
        (fun v => chainVertexWeight D z v) := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hwone,
      Finset.affineCombination_eq_linear_combination _ _ _ hzone]
    rw [Finset.sum_coe_sort s (fun v => chainVertexWeight C w v • v),
      Finset.sum_coe_sort s (fun v => chainVertexWeight D z v • v)]
    exact (sum_smul_barycenter_eq_chainVertexWeight hCs w).symm.trans
        (heq.trans (sum_smul_barycenter_eq_chainVertexWeight hDs z))
  intro v hv
  exact ((Q.indep hs).affineCombination_eq_iff_eq hwone hzone).mp he
    ⟨v, hv⟩ (Finset.mem_univ _)

/-- For [two face chains](hyp:hC,hD), [strictly positive weights on each
chain](hyp:hw,hz) [summing to one](hyp:hsw,hsz) that [give the same weighted
barycenter](hyp:heq) [force the chains to coincide](goal). -/
theorem faceChain_positive_support_unique {Q : Geometry.SimplicialComplex ℝ E}
    {C D : Finset (Finset E)} (hC : IsFaceChain Q C) (hD : IsFaceChain Q D)
    {w z : Finset E → ℝ} (hw : ∀ s ∈ C, 0 < w s) (hz : ∀ s ∈ D, 0 < z s)
    (hsw : ∑ s ∈ C, w s = 1) (hsz : ∑ s ∈ D, z s = 1)
    (heq : ∑ s ∈ C, w s • barycenter s = ∑ s ∈ D, z s • barycenter s) :
    C = D := by
  classical
  obtain ⟨s, hsC, hmax⟩ := C.exists_max_image Finset.card hC.1
  have hs := hC.2.1 s hsC
  have hCs : ∀ t ∈ C, t ⊆ s := by
    intro t ht
    rcases hC.2.2 t ht s hsC with h | h
    · exact h
    · exact (Finset.eq_of_subset_of_card_le h (hmax t ht)).symm.subset
  have hx : (∑ t ∈ C, w t • barycenter t) ∈ convexHull ℝ (s : Set E) :=
    (convex_convexHull ℝ _).sum_mem (fun t ht => (hw t ht).le) hsw
      (fun t ht => convexHull_mono (hCs t ht)
        (barycenter_mem_convexHull (Q.nonempty_of_mem_faces (hC.2.1 t ht))))
  have hDs : ∀ t ∈ D, t ⊆ s :=
    faceChain_weighted_sum_carrier hD hz hsz hs (heq ▸ hx)
  have hcoord := faceChain_coordinates_eq hC hD hs hCs hDs hsw hsz heq
  apply chainVertexWeight_unique
    (fun t ht => Q.nonempty_of_mem_faces (hC.2.1 t ht))
    (fun t ht => Q.nonempty_of_mem_faces (hD.2.1 t ht)) hC.2.2 hD.2.2 hw hz
  funext v
  by_cases hv : v ∈ s
  · exact hcoord v hv
  · have hzero (A : Finset (Finset E)) (b : Finset E → ℝ)
        (hA : ∀ t ∈ A, t ⊆ s) : chainVertexWeight A b v = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      simp [show v ∉ t from fun hvt => hv (hA t ht hvt)]
    rw [hzero C w hCs, hzero D z hDs]

open Classical in
/-- If [a simplex belongs to a complex](hyp:hs) and [a point lies in its
convex hull](hyp:hx), [a chain of its nonempty subfaces has a barycenter hull
containing that point](goal). -/
theorem exists_faceChain_cover {Q : Geometry.SimplicialComplex ℝ E}
    {s : Finset E} (hs : s ∈ Q.faces) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) :
    ∃ C : Finset (Finset E), IsFaceChain Q C ∧
      (∀ t ∈ C, t ⊆ s) ∧ x ∈ convexHull ℝ (C.image barycenter : Set E) := by
  classical
  obtain ⟨a, ha, hsum, hax⟩ := Finset.mem_convexHull'.mp hx
  obtain ⟨C, hCne, hsub, hchain, w, hw, hwone, hcoords⟩ :=
    exists_chainVertexWeight ha hsum
  have hC : IsFaceChain Q C := ⟨hCne,
    fun t ht => Q.down_closed hs (hsub t ht).2 (hsub t ht).1, hchain⟩
  refine ⟨C, hC, fun t ht => (hsub t ht).2, ?_⟩
  have hpoint : ∑ t ∈ C, w t • barycenter t = x := by
    rw [sum_smul_barycenter_eq_chainVertexWeight (fun t ht => (hsub t ht).2)]
    exact (Finset.sum_congr rfl (fun v hv => by rw [hcoords v hv])).trans hax
  rw [← hpoint]
  exact (convex_convexHull ℝ _).sum_mem (fun t ht => (hw t ht).le) hwone
    (fun t ht => subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩))

/-- If [two finite sets are barycentric faces](hyp:hs,ht), [their convex hulls
intersect only in the convex hull of their shared vertices](goal). -/
theorem barycentricFaces_inter {Q : Geometry.SimplicialComplex ℝ E}
    {s t : Finset E} (hs : s ∈ barycentricFaces Q) (ht : t ∈ barycentricFaces Q) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ (s ∩ t : Set E) := by
  -- Take convex weights for a point in both hulls and remove zero weights.
  -- Injectivity of barycenter on Q.faces lifts these to positive chain weights.
  -- faceChain_positive_support_unique identifies the remaining chains, so all
  -- active barycenters belong to the intersection of the two vertex sets.
  classical
  intro x hx
  have extract : ∀ {A : Finset (Finset E)}, IsFaceChain Q A →
      x ∈ convexHull ℝ (A.image barycenter : Set E) →
      ∃ B : Finset (Finset E), B ⊆ A ∧ IsFaceChain Q B ∧
        ∃ w : Finset E → ℝ, (∀ u ∈ B, 0 < w u) ∧
          (∑ u ∈ B, w u = 1) ∧ ∑ u ∈ B, w u • barycenter u = x := by
    intro A hA hxA
    obtain ⟨a, ha, haone, hax⟩ := Finset.mem_convexHull'.mp hxA
    have hinj : Set.InjOn barycenter (A : Set (Finset E)) := by
      intro u hu v hv he
      exact barycenter_injective_on_faces (hA.2.1 u hu) (hA.2.1 v hv) he
    have hsum : ∑ u ∈ A, a (barycenter u) = 1 := by
      rw [← Finset.sum_image hinj]
      exact haone
    have hpoint : ∑ u ∈ A, a (barycenter u) • barycenter u = x := by
      rw [← Finset.sum_image (f := fun y => a y • y) hinj]
      exact hax
    let B := A.filter (fun u => 0 < a (barycenter u))
    have hBA : B ⊆ A := Finset.filter_subset _ _
    have hzero : ∀ u ∈ A, u ∉ B → a (barycenter u) = 0 := by
      intro u hu huB
      have hn := ha (barycenter u) (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
      have hnp : ¬ 0 < a (barycenter u) := by
        intro hp
        exact huB (Finset.mem_filter.mpr ⟨hu, hp⟩)
      exact le_antisymm (le_of_not_gt hnp) hn
    have hBone : ∑ u ∈ B, a (barycenter u) = 1 := by
      rw [Finset.sum_subset hBA (fun u hu huB => hzero u hu huB)]
      exact hsum
    have hBpoint : ∑ u ∈ B, a (barycenter u) • barycenter u = x := by
      rw [Finset.sum_subset hBA (fun u hu huB => by rw [hzero u hu huB, zero_smul])]
      exact hpoint
    have hBne : B.Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hBone
      norm_num at hBone
    exact ⟨B, hBA, ⟨hBne, fun u hu => hA.2.1 u (hBA hu),
      fun u hu v hv => hA.2.2 u (hBA hu) v (hBA hv)⟩,
      fun u => a (barycenter u), fun u hu => (Finset.mem_filter.mp hu).2,
      hBone, hBpoint⟩
  obtain ⟨C, hC, rfl⟩ := hs
  obtain ⟨D, hD, rfl⟩ := ht
  obtain ⟨A, hAC, hA, w, hw, hwone, hwx⟩ := extract hC hx.1
  obtain ⟨B, hBD, hB, z, hz, hzone, hzx⟩ := extract hD hx.2
  have hAB := faceChain_positive_support_unique hA hB hw hz hwone hzone
    (hwx.trans hzx.symm)
  rw [← hwx]
  apply (convex_convexHull ℝ _).sum_mem (fun u hu => (hw u hu).le) hwone
  intro u hu
  apply subset_convexHull ℝ _
  exact ⟨Finset.mem_image.mpr ⟨u, hAC hu, rfl⟩,
    Finset.mem_image.mpr ⟨u, hBD (hAB ▸ hu), rfl⟩⟩

/-- The [geometric barycentric subdivision](goal) of [a complex](hyp:Q) in
[a real normed space](hyp:E) has [the barycenter sets of face chains as its
faces](step:1), with [affine independence](step:2), [closure under nonempty
subsets](step:3), and [convex hulls intersecting only along common faces](step:4). -/
noncomputable def sd (Q : Geometry.SimplicialComplex ℝ E) :
    Geometry.SimplicialComplex ℝ E where
  faces := barycentricFaces Q
  indep := barycentricFaces_independent
  isRelLowerSet_faces := barycentricFaces_down_closed Q
  inter_subset_convexHull := barycentricFaces_inter

/-- The subdivision of [a complex](hyp:Q) [has exactly the barycenters of the
original faces as its vertices](goal). -/
theorem sd_vertices (Q : Geometry.SimplicialComplex ℝ E) :
    (sd Q).vertices = barycenter '' Q.faces := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨C, hC, he⟩ := (sd Q).mem_vertices.mp hx
    have hxC : x ∈ C.image barycenter := he ▸ Finset.mem_singleton_self x
    obtain ⟨s, hs, hxs⟩ := Finset.mem_image.mp hxC
    exact ⟨s, hC.2.1 s hs, hxs⟩
  · rintro ⟨s, hs, rfl⟩
    apply (sd Q).mem_vertices.mpr
    refine ⟨{s}, ⟨Finset.singleton_nonempty s, ?_, ?_⟩, ?_⟩
    · simpa using hs
    · intro u hu v hv
      simp only [Finset.mem_singleton] at hu hv
      subst u
      subst v
      exact Or.inl Finset.Subset.rfl
    · simp

/-- If [a simplex belongs to the subdivision](hyp:hs), [it is contained in an
original simplex](goal). -/
theorem sd_face_subset {Q : Geometry.SimplicialComplex ℝ E} {s : Finset E}
    (hs : s ∈ (sd Q).faces) :
    ∃ t ∈ Q.faces, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  classical
  obtain ⟨C, hC, rfl⟩ := hs
  obtain ⟨t, ht, hmax⟩ := C.exists_max_image Finset.card hC.1
  refine ⟨t, hC.2.1 t ht, convexHull_min ?_ (convex_convexHull ℝ _)⟩
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  have hut : u ⊆ t := by
    rcases hC.2.2 u hu t ht with h | h
    · exact h
    · exact (Finset.eq_of_subset_of_card_le h (hmax u hu)).symm.subset
  exact convexHull_mono hut (barycenter_mem_convexHull
    (Q.nonempty_of_mem_faces (hC.2.1 u hu)))

/-- The subdivision of [a geometric complex](hyp:Q) [has exactly the same
underlying space](goal). -/
theorem sd_space (Q : Geometry.SimplicialComplex ℝ E) : (sd Q).space = Q.space := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := (sd Q).mem_space_iff.mp hx
    obtain ⟨t, ht, hst⟩ := sd_face_subset hs
    exact Q.convexHull_subset_space ht (hst hxs)
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Q.mem_space_iff.mp hx
    obtain ⟨C, hC, _, hxC⟩ := exists_faceChain_cover hs hxs
    exact (sd Q).mem_space_iff.mpr ⟨C.image barycenter, ⟨C, hC, rfl⟩, hxC⟩

/-- If [a complex has finitely many faces](hyp:hQ), [its subdivision also has
finitely many faces](goal). -/
theorem sd_finite {Q : Geometry.SimplicialComplex ℝ E} (hQ : Q.faces.Finite) :
    (sd Q).faces.Finite := by
  classical
  apply ((hQ.toFinset.powerset.finite_toSet).image
    (fun C : Finset (Finset E) => C.image barycenter)).subset
  rintro s ⟨C, hC, rfl⟩
  refine ⟨C, Finset.mem_powerset.mpr ?_, rfl⟩
  intro t ht
  exact hQ.mem_toFinset.mpr (hC.2.1 t ht)

end Toolkit.Foundations.Topology
