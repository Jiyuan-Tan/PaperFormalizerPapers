module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Data.Sign.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Logic.Nonempty
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.UniformSpace.Defs

/-!
# Affine general position relative to zero by small perturbations

A set of points of a real vector space is in general position relative to zero when its
affine span either misses zero or is the whole space. This module provides the
perturbation steps that put finitely many configurations of chosen points into that
position:

* `exists_proper_affineSubspace_for_insert`: the points whose adjunction breaks the
  property lie in one proper affine subspace;
* `exists_near_avoiding_affineSubspaces`: in a finite-dimensional space, every ball meets
  the complement of finitely many proper affine subspaces (they are Haar-null,
  `MeasureTheory.Measure.addHaar_affineSubspace`);
* `exists_near_simultaneous_insert`: one point near a given centre can be adjoined to
  finitely many configurations, each after its own invertible linear change of coordinates;
* `exists_generalPosition_coordinates`: values in prescribed nonempty open sets put finitely
  many configurations of shared coordinates, each transformed by invertible linear maps,
  in general position relative to zero.

Only the forbidden choices at each step form a finite union of proper affine subspaces;
the global rank-deficiency locus need not be such a union, hence the coordinate-by-coordinate
induction.
-/

public section

namespace Toolkit.Foundations.LinearAlgebra

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For [a set of target values](hyp:S) whose [affine span either misses zero
or fills the target](hyp:hS), [there is a proper affine subspace such that
adjoining any point outside it preserves that alternative](goal). -/
theorem exists_proper_affineSubspace_for_insert (S : Set F)
    (hS : 0 ∈ affineSpan ℝ S → affineSpan ℝ S = ⊤) :
    ∃ A : AffineSubspace ℝ F, A ≠ ⊤ ∧ ∀ y : F, y ∉ A →
      0 ∈ affineSpan ℝ (insert y S) → affineSpan ℝ (insert y S) = ⊤ := by
  classical
  by_cases hB : affineSpan ℝ S = ⊤
  · refine ⟨⊥, bot_ne_top, fun y _ _ => ?_⟩
    exact top_unique (hB ▸ affineSpan_mono ℝ (Set.subset_insert y S))
  by_cases hC : affineSpan ℝ (insert 0 S) = ⊤
  · refine ⟨affineSpan ℝ S, hB, fun y _ h0 => ?_⟩
    apply top_unique
    rw [← hC]
    apply affineSpan_le.2
    exact Set.insert_subset h0 (fun x hx => mem_affineSpan ℝ (Set.mem_insert_of_mem y hx))
  refine ⟨affineSpan ℝ (insert 0 S), hC, fun y hy h0 => ?_⟩
  exfalso
  apply hy
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp⟩ := hne
    have hpB := mem_affineSpan ℝ hp
    rw [← affineSpan_insert_affineSpan] at h0
    obtain ⟨r, q, hq, heq⟩ :=
      (AffineSubspace.mem_affineSpan_insert_iff hpB y 0).1 h0
    have hr : r ≠ 0 := by
      intro hr
      simp only [hr, zero_smul, zero_vadd] at heq
      exact hB (hS (heq ▸ hq))
    have hpC : p ∈ affineSpan ℝ (insert 0 S) :=
      mem_affineSpan ℝ (Set.mem_insert_of_mem 0 hp)
    have hqC : q ∈ affineSpan ℝ (insert 0 S) :=
      affineSpan_mono ℝ (Set.subset_insert 0 S) hq
    have hzC : (0 : F) ∈ affineSpan ℝ (insert 0 S) := mem_affineSpan ℝ (Set.mem_insert 0 S)
    have hyC := (affineSpan ℝ (insert 0 S)).smul_vsub_vadd_mem r⁻¹ hzC hqC hpC
    convert hyC using 1
    change y = r⁻¹ • (0 - q) + p
    have heq' : r • (y - p) = 0 - q := by
      exact eq_sub_iff_add_eq.mpr heq.symm
    rw [← heq', smul_smul, inv_mul_cancel₀ hr, one_smul, sub_add_cancel]
  · have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst S
    simpa [eq_comm] using h0

variable [FiniteDimensional ℝ F]

/-- Given [finitely many affine subspaces](hyp:S), [each proper](hyp:hS),
[a center point](hyp:c), and [a positive tolerance](hyp:hε), [some point within
that tolerance avoids every one of the subspaces](goal). -/
theorem exists_near_avoiding_affineSubspaces (S : Finset (AffineSubspace ℝ F))
    (hS : ∀ A ∈ S, A ≠ ⊤) (c : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : F, dist y c < ε ∧ ∀ A ∈ S, y ∉ A := by
  classical
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let μ : MeasureTheory.Measure F := MeasureTheory.Measure.addHaar
  have hnull : μ (⋃ A ∈ S, (A : Set F)) = 0 :=
    (MeasureTheory.measure_biUnion_null_iff S.countable_toSet).2 fun A hA =>
      MeasureTheory.Measure.addHaar_affineSubspace μ A (hS A hA)
  by_contra! h
  have hsub : Metric.ball c ε ⊆ ⋃ A ∈ S, (A : Set F) := by
    intro y hy
    obtain ⟨A, hA, hyA⟩ := h y hy
    exact Set.mem_iUnion.2 ⟨A, Set.mem_iUnion.2 ⟨hA, hyA⟩⟩
  exact (Metric.measure_ball_pos μ c hε).ne'
    (MeasureTheory.measure_mono_null hsub hnull)

/-- Given [finitely many sets of target values](hyp:S), [an invertible linear
change of coordinates for each set](hyp:L), and [affine spans that each miss
zero or fill the target](hyp:hS), fix [a center](hyp:c) and [a positive
tolerance](hyp:hε). Then [there is a point within that tolerance of the center
that can be adjoined in each change of coordinates while preserving all
these alternatives](goal). -/
theorem exists_near_simultaneous_insert {ι : Type*} [Finite ι]
    (S : ι → Set F) (L : ι → F ≃ₗ[ℝ] F)
    (hS : ∀ i, 0 ∈ affineSpan ℝ (S i) → affineSpan ℝ (S i) = ⊤)
    (c : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : F, dist y c < ε ∧ ∀ i,
      0 ∈ affineSpan ℝ (insert (L i y) (S i)) →
        affineSpan ℝ (insert (L i y) (S i)) = ⊤ := by
  classical
  let := Fintype.ofFinite ι
  choose A hA hgood using fun i => exists_proper_affineSubspace_for_insert (S i) (hS i)
  let B (i : ι) := (A i).comap (L i).toLinearMap.toAffineMap
  have hB (i : ι) : B i ≠ ⊤ := by
    intro h
    apply hA i
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := (L i).surjective x
    have hy : y ∈ B i := by rw [h]; trivial
    exact hy
  obtain ⟨y, hy, havoid⟩ := exists_near_avoiding_affineSubspaces
    (Finset.univ.image B) (by simpa using hB) c hε
  refine ⟨y, hy, fun i => hgood i (L i y) ?_⟩
  exact havoid (B i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- Given [a finite set of coordinate indices](hyp:I), [finitely many
configurations](hyp:s) [using only those indices](hyp:hsub), [invertible
linear transformations for their occurrences](hyp:L), and [coordinate
neighborhoods](hyp:U) that [are open](hyp:hU) and [nonempty](hyp:hne),
[values can be chosen in those neighborhoods so each transformed
configuration has affine span missing zero or filling the target](goal). -/
theorem exists_generalPosition_coordinates {ι κ : Type*} [Finite κ]
    (I : Finset ι) (s : κ → Finset ι) (hsub : ∀ j, s j ⊆ I)
    (L : κ → ι → F ≃ₗ[ℝ] F) (U : ι → Set F)
    (hU : ∀ i ∈ I, IsOpen (U i)) (hne : ∀ i ∈ I, (U i).Nonempty) :
    ∃ w : ι → F, (∀ i ∈ I, w i ∈ U i) ∧ ∀ j,
      0 ∈ affineSpan ℝ ((fun i => L j i (w i)) '' (s j : Set ι)) →
        affineSpan ℝ ((fun i => L j i (w i)) '' (s j : Set ι)) = ⊤ := by
  -- Induct on I, generalizing the configurations. On inserting a coordinate i,
  -- the other values come from the induction hypothesis (applied to the
  -- configurations with i erased), and the value at i comes from
  -- exists_near_simultaneous_insert over the configurations containing i.
  classical
  induction I using Finset.induction_on generalizing s with
  | empty =>
      refine ⟨fun _ => 0, by simp, ?_⟩
      intro j
      have hs : s j = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
        (fun i hi => by simpa using hsub j hi)
      simp only [hs, Finset.coe_empty, Set.image_empty, AffineSubspace.span_empty]
      intro h
      exact (AffineSubspace.notMem_bot ℝ F 0 h).elim
  | @insert i I hi ih =>
      have hsub' : ∀ j, (s j).erase i ⊆ I := by
        intro j k hk
        have hk' := Finset.mem_erase.mp hk
        exact (Finset.mem_insert.mp (hsub j hk'.2)).resolve_left hk'.1
      obtain ⟨w, hw, hgood⟩ := ih (fun j => (s j).erase i) hsub'
        (fun k hk => hU k (Finset.mem_insert_of_mem hk))
        (fun k hk => hne k (Finset.mem_insert_of_mem hk))
      obtain ⟨c, hc⟩ := hne i (Finset.mem_insert_self i I)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
        (hU i (Finset.mem_insert_self i I)) c hc
      obtain ⟨y, hy, hygood⟩ := exists_near_simultaneous_insert
        (fun j : {j : κ // i ∈ s j} =>
          (fun k => L j.val k (w k)) '' ((s j.val).erase i : Set ι))
        (fun j => L j.val i) (fun j => hgood j.val) c hε
      refine ⟨Function.update w i y, ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simpa using hball hy
        · rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hi)]
          exact hw k hk
      · intro j
        have herase :
            (fun k => L j k (Function.update w i y k)) ''
                ((s j).erase i : Set ι) =
              (fun k => L j k (w k)) '' ((s j).erase i : Set ι) := by
          apply Set.image_congr
          intro k hk
          rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
        by_cases hij : i ∈ s j
        · have hs : (s j : Set ι) = insert i ((s j).erase i : Set ι) := by
            simpa using congrArg (fun t : Finset ι => (t : Set ι))
              (Finset.insert_erase hij).symm
          rw [hs, Set.image_insert_eq, herase, Function.update_self]
          exact hygood ⟨j, hij⟩
        · have hs : (s j).erase i = s j := Finset.erase_eq_of_notMem hij
          rw [← hs, herase]
          exact hgood j

end Toolkit.Foundations.LinearAlgebra

namespace Toolkit.Foundations.LinearAlgebra

section

open Set
variable {E V : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]

/-- If [a finite set of points is affinely independent](hyp:hs), [any assignment
of values in a real vector space to those points extends to an affine map on
the entire ambient space](goal). -/
-- @node: exists_affine_extension_module
lemma exists_affineMap_eq_of_affineIndependent {s : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (v : s → V) :
    ∃ a : E →ᵃ[ℝ] V, ∀ p : s, a p = v p := by
  classical
  by_cases hempty : IsEmpty s
  · exact ⟨AffineMap.const ℝ E 0, fun p => (hempty.false p).elim⟩
  · have : Nonempty s := not_isEmpty_iff.mp hempty
    let p₀ : s := Classical.choice inferInstance
    let w : {p : s // p ≠ p₀} → E := fun p => (p.val : E) - p₀
    have hw : LinearIndependent ℝ w :=
      (affineIndependent_iff_linearIndependent_vsub ℝ _ p₀).mp hs
    let b := Module.Basis.extend hw.linearIndepOn_id
    let L : E →ₗ[ℝ] V := b.constr ℝ
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

end

end Toolkit.Foundations.LinearAlgebra

namespace Toolkit.Foundations.LinearAlgebra

section

open Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- If [a family of affine subspaces is countable](hyp:hcount), [every member is
proper](hyp:hS), and [the radius is positive](hyp:heps), then [there is a point
within that radius of the prescribed center that belongs to none of the affine
subspaces](goal). -/
-- @node: exists_near_avoiding_countable_affineSubspaces
lemma exists_near_avoiding_countable_affineSubspaces
    (S : Set (AffineSubspace ℝ F)) (hcount : S.Countable)
    (hS : ∀ A ∈ S, A ≠ ⊤) (c : F) {eps : ℝ} (heps : 0 < eps) :
    ∃ y : F, dist y c < eps ∧ ∀ A ∈ S, y ∉ A := by
  classical
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let μ : MeasureTheory.Measure F := MeasureTheory.Measure.addHaar
  have hnull : μ (⋃ A ∈ S, (A : Set F)) = 0 :=
    (MeasureTheory.measure_biUnion_null_iff hcount).2 fun A hA =>
      MeasureTheory.Measure.addHaar_affineSubspace μ A (hS A hA)
  by_contra! h
  have hsub : Metric.ball c eps ⊆ ⋃ A ∈ S, (A : Set F) := by
    intro y hy
    obtain ⟨A, hA, hyA⟩ := h y hy
    exact mem_iUnion.2 ⟨A, mem_iUnion.2 ⟨hA, hyA⟩⟩
  exact (Metric.measure_ball_pos μ c heps).ne'
    (MeasureTheory.measure_mono_null hsub hnull)

end

end Toolkit.Foundations.LinearAlgebra
