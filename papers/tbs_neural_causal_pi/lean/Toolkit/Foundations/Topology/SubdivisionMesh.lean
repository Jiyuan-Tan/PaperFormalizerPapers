module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.Closure
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.UniformSpace.Defs
public import Toolkit.Foundations.Topology.BarycentricSubdivision

/-!
# Mesh of iterated barycentric subdivisions

The dimension and the mesh (largest face diameter) of a geometric simplicial complex, the
iterated subdivision `sdIterate Q k`, and the classical mesh bound (Munkres, *Elements of
Algebraic Topology*, Lemma 15.4):

* `dist_barycenter_le`: the barycenters of nested faces are close;
* `mesh_sd_le`: `mesh (sd Q) ≤ d / (d + 1) * mesh Q` with `d` the dimension of `Q`;
* `mesh_sdIterate_le`, `mesh_sdIterate_tendsto_zero`: the mesh of `sd^[k] Q` tends to zero;
* `sdIterate_space`, `sdIterate_finite`, `sdIterate_face_subset`.

Mesh and dimension are zero on the empty complex.
-/

@[expose] public section

namespace Toolkit.Foundations.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For [a geometric complex](hyp:Q) in [a real normed space](hyp:E), its
[dimension](goal) is the supremum of face cardinalities minus one; for a
finite complex this is the largest such number, with zero for the empty complex. -/
noncomputable def dimension (Q : Geometry.SimplicialComplex ℝ E) : ℕ :=
  sSup ((fun s : Finset E => s.card - 1) '' Q.faces)

/-- For [a geometric complex](hyp:Q) in [a real normed space](hyp:E), its
[mesh](goal) is the real supremum of its face diameters together with zero;
for a finite complex this is the largest face diameter, or zero if empty. -/
noncomputable def mesh (Q : Geometry.SimplicialComplex ℝ E) : ℝ :=
  sSup (insert 0 ((fun s : Finset E => Metric.diam (convexHull ℝ (s : Set E))) '' Q.faces))

/-- Subdividing [a complex](hyp:Q) in [a real normed space](hyp:E)
[a prescribed number of times](hyp:k)
gives [the iterated subdivision](goal), [starting at the original complex](step:1)
and [applying one further barycentric subdivision at every step](step:2). -/
noncomputable def sdIterate (Q : Geometry.SimplicialComplex ℝ E) :
    (k : ℕ) → Geometry.SimplicialComplex ℝ E
  | 0 => Q
  | k + 1 => sd (sdIterate Q k)

/-- Every [iterate](hyp:k) of [a complex](hyp:Q) [has the original underlying
space](goal). -/
theorem sdIterate_space (Q : Geometry.SimplicialComplex ℝ E) (k : ℕ) :
    (sdIterate Q k).space = Q.space := by
  induction k with
  | zero => rfl
  | succ k ih => exact (sd_space (sdIterate Q k)).trans ih

/-- If [a complex has finitely many faces](hyp:hQ), [each iterated
subdivision has finitely many faces](goal). -/
theorem sdIterate_finite {Q : Geometry.SimplicialComplex ℝ E} (hQ : Q.faces.Finite)
    (k : ℕ) : (sdIterate Q k).faces.Finite := by
  induction k with
  | zero => exact hQ
  | succ k ih => exact sd_finite ih

/-- If [a simplex belongs to an iterated subdivision](hyp:hs), [it is
contained in a face of the original complex](goal). -/
theorem sdIterate_face_subset {Q : Geometry.SimplicialComplex ℝ E} (k : ℕ)
    {s : Finset E} (hs : s ∈ (sdIterate Q k).faces) :
    ∃ t ∈ Q.faces, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  induction k generalizing s with
  | zero => exact ⟨s, hs, Set.Subset.rfl⟩
  | succ k ih =>
    obtain ⟨t, ht, hst⟩ := sd_face_subset hs
    obtain ⟨u, hu, htu⟩ := ih ht
    exact ⟨u, hu, hst.trans htu⟩

/-- If [one nonempty vertex set is contained in another](hyp:hs,hst),
[the distance between their barycenters is at most the diameter of the larger
set's convex hull multiplied by the fraction of its vertices outside the smaller
set](goal). -/
theorem dist_barycenter_le {s t : Finset E} (hs : s.Nonempty) (hst : s ⊆ t) :
    dist (barycenter s) (barycenter t) ≤
      ((t.card - s.card : ℕ) : ℝ) / (t.card : ℝ) * Metric.diam (convexHull ℝ (t : Set E)) := by
  classical
  by_cases he : s = t
  · subst t
    simp
  have hd : (t \ s).Nonempty := Finset.sdiff_nonempty.mpr
    (fun h => he (Finset.Subset.antisymm hst h))
  have hs0 : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_ne_zero
  have ht0 : (t.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (hs.mono hst).card_ne_zero
  have hd0 : ((t \ s).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.card_ne_zero
  -- Clear the normalization, then split the vertex sum over s and t \ s.
  have hmass (u : Finset E) (hu : (u.card : ℝ) ≠ 0) :
      (u.card : ℝ) • barycenter u = ∑ x ∈ u, x := by
    simp [barycenter, Finset.centerMass, smul_smul, hu]
  have hsum : ∑ x ∈ t, x =
      (s.card : ℝ) • barycenter s + ((t \ s).card : ℝ) • barycenter (t \ s) := by
    rw [hmass s hs0, hmass (t \ s) hd0, add_comm]
    exact (Finset.sum_sdiff hst).symm
  have hcards : (s.card : ℝ) + ((t \ s).card : ℝ) = (t.card : ℝ) := by
    exact_mod_cast (by simpa only [add_comm] using
      Finset.card_sdiff_add_card_eq_card hst)
  have hcoef : (t.card : ℝ)⁻¹ * (s.card : ℝ) =
      1 - ((t \ s).card : ℝ) / (t.card : ℝ) := by
    apply (eq_sub_iff_add_eq).mpr
    rw [div_eq_inv_mul, ← mul_add, hcards, inv_mul_cancel₀ ht0]
  have hsplit : barycenter t =
      (1 - ((t \ s).card : ℝ) / (t.card : ℝ)) • barycenter s +
      (((t \ s).card : ℝ) / (t.card : ℝ)) • barycenter (t \ s) := by
    calc
      barycenter t = (t.card : ℝ)⁻¹ • ∑ x ∈ t, x := by
        simp [barycenter, Finset.centerMass]
      _ = _ := by rw [hsum, smul_add, smul_smul, smul_smul, hcoef, ← div_eq_inv_mul]
  -- Subtracting the first barycenter leaves a nonnegative scalar displacement.
  have hdispl : barycenter t - barycenter s =
      (((t \ s).card : ℝ) / (t.card : ℝ)) •
        (barycenter (t \ s) - barycenter s) := by
    rw [hsplit, sub_smul, one_smul, smul_sub]
    abel
  have hbound : dist (barycenter (t \ s)) (barycenter s) ≤
      Metric.diam (convexHull ℝ (t : Set E)) :=
    Metric.dist_le_diam_of_mem
      (isBounded_convexHull.mpr t.finite_toSet.isBounded)
      (convexHull_mono Finset.sdiff_subset (barycenter_mem_convexHull hd))
      (convexHull_mono hst (barycenter_mem_convexHull hs))
  rw [dist_comm, dist_eq_norm, hdispl, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  simpa only [Finset.card_sdiff_of_subset hst, dist_eq_norm] using
    mul_le_mul_of_nonneg_left hbound
      (div_nonneg (Nat.cast_nonneg (t \ s).card) (Nat.cast_nonneg t.card))

/-- If [a complex has finitely many faces](hyp:hQ), [subdivision does not
increase its dimension](goal). -/
theorem dimension_sd_le {Q : Geometry.SimplicialComplex ℝ E} (hQ : Q.faces.Finite) :
    dimension (sd Q) ≤ dimension Q := by
  classical
  unfold dimension
  apply csSup_le'
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨C, hC, rfl⟩ := hu
  obtain ⟨t, ht, hmax⟩ := C.exists_max_image Finset.card hC.1
  -- Comparable finite sets with equal cardinality coincide, so cardinality
  -- embeds the chain into the positive integers up to the largest face size.
  have hcard : C.card ≤ t.card := by
    calc
      C.card ≤ (Finset.Icc 1 t.card).card := by
        apply Finset.card_le_card_of_injOn Finset.card
        · intro s hs
          exact Finset.mem_Icc.mpr
            ⟨(Q.nonempty_of_mem_faces (hC.2.1 s hs)).card_pos, hmax s hs⟩
        · intro s hs v hv he
          rcases hC.2.2 s hs v hv with h | h
          · exact Finset.eq_of_subset_of_card_le h he.ge
          · exact (Finset.eq_of_subset_of_card_le h he.le).symm
      _ = t.card := by simp
  exact (Nat.sub_le_sub_right ((Finset.card_image_le).trans hcard) 1).trans
    (le_csSup (hQ.image (fun s : Finset E => s.card - 1)).bddAbove
      ⟨t, hC.2.1 t ht, rfl⟩)

/-- If [a complex has finitely many faces](hyp:hQ), [its mesh is
nonnegative](goal). -/
theorem mesh_nonneg {Q : Geometry.SimplicialComplex ℝ E} (hQ : Q.faces.Finite) :
    0 ≤ mesh Q := by
  exact le_csSup ((hQ.image _).insert 0).bddAbove (Set.mem_insert 0 _)

/-- If [a complex has finitely many faces](hyp:hQ), [its subdivision contracts
mesh by its dimension divided by one plus its dimension](goal). -/
theorem mesh_sd_le {Q : Geometry.SimplicialComplex ℝ E} (hQ : Q.faces.Finite) :
    mesh (sd Q) ≤ (dimension Q : ℝ) / ((dimension Q : ℝ) + 1) * mesh Q := by
  classical
  have hmesh := mesh_nonneg hQ
  have hfactor : 0 ≤ (dimension Q : ℝ) / ((dimension Q : ℝ) + 1) :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hface (t : Finset E) (ht : t ∈ Q.faces) :
      Metric.diam (convexHull ℝ (t : Set E)) ≤ mesh Q :=
    le_csSup ((hQ.image _).insert 0).bddAbove (Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩)
  have hpair (u v : Finset E) (hu : u ∈ Q.faces) (hv : v ∈ Q.faces)
      (huv : u ⊆ v) : dist (barycenter u) (barycenter v) ≤
      (dimension Q : ℝ) / ((dimension Q : ℝ) + 1) * mesh Q := by
    have hu1 := (Q.nonempty_of_mem_faces hu).card_pos
    have huvcard := Finset.card_le_card huv
    have hvdim : v.card - 1 ≤ dimension Q :=
      le_csSup (hQ.image (fun s : Finset E => s.card - 1)).bddAbove ⟨v, hv, rfl⟩
    have hvbound : (v.card : ℝ) ≤ (dimension Q : ℝ) + 1 := by
      exact_mod_cast (show v.card ≤ dimension Q + 1 by omega)
    have hvpos : (0 : ℝ) < v.card := by exact_mod_cast (by omega : 0 < v.card)
    have hsub : ((v.card - u.card : ℕ) : ℝ) = (v.card : ℝ) - (u.card : ℝ) :=
      Nat.cast_sub huvcard
    have huone : (1 : ℝ) ≤ u.card := by exact_mod_cast hu1
    have hratio : ((v.card - u.card : ℕ) : ℝ) / (v.card : ℝ) ≤
        (dimension Q : ℝ) / ((dimension Q : ℝ) + 1) := by
      rw [div_le_div_iff₀ hvpos (by positivity), hsub]
      nlinarith [mul_nonneg (sub_nonneg.mpr huone)
        (show 0 ≤ (dimension Q : ℝ) + 1 by positivity)]
    exact (dist_barycenter_le (Q.nonempty_of_mem_faces hu) huv).trans
      ((mul_le_mul_of_nonneg_right hratio Metric.diam_nonneg).trans
        (mul_le_mul_of_nonneg_left (hface v hv) hfactor))
  apply csSup_le (Set.insert_nonempty 0 _)
  intro a ha
  rcases Set.mem_insert_iff.mp ha with rfl | ⟨s, hs, rfl⟩
  · exact mul_nonneg hfactor hmesh
  obtain ⟨C, hC, rfl⟩ := hs
  dsimp only
  rw [convexHull_diam]
  apply Metric.diam_le_of_forall_dist_le (mul_nonneg hfactor hmesh)
  intro x hx y hy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  rcases hC.2.2 u hu v hv with huv | hvu
  · exact hpair u v (hC.2.1 u hu) (hC.2.1 v hv) huv
  · rw [dist_comm]
    exact hpair v u (hC.2.1 v hv) (hC.2.1 u hu) hvu

/-- If [a complex has finitely many faces](hyp:hQ), [the mesh after any
number of subdivisions is bounded by the corresponding power of the original
contraction factor times its original mesh](goal). -/
theorem mesh_sdIterate_le {Q : Geometry.SimplicialComplex ℝ E} (hQ : Q.faces.Finite)
    (k : ℕ) : mesh (sdIterate Q k) ≤
      ((dimension Q : ℝ) / ((dimension Q : ℝ) + 1)) ^ k * mesh Q := by
  have hdim (n : ℕ) : dimension (sdIterate Q n) ≤ dimension Q := by
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact (dimension_sd_le (sdIterate_finite hQ n)).trans ih
  have hfactor : 0 ≤ (dimension Q : ℝ) / ((dimension Q : ℝ) + 1) :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  induction k with
  | zero => simp [sdIterate]
  | succ k ih =>
    have hmono : (dimension (sdIterate Q k) : ℝ) /
        ((dimension (sdIterate Q k) : ℝ) + 1) ≤
        (dimension Q : ℝ) / ((dimension Q : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hd : (dimension (sdIterate Q k) : ℝ) ≤ (dimension Q : ℝ) :=
        Nat.cast_le.mpr (hdim k)
      nlinarith
    calc
      mesh (sdIterate Q (k + 1)) ≤
          (dimension (sdIterate Q k) : ℝ) /
            ((dimension (sdIterate Q k) : ℝ) + 1) * mesh (sdIterate Q k) :=
        mesh_sd_le (sdIterate_finite hQ k)
      _ ≤ (dimension Q : ℝ) / ((dimension Q : ℝ) + 1) * mesh (sdIterate Q k) :=
        mul_le_mul_of_nonneg_right hmono (mesh_nonneg (sdIterate_finite hQ k))
      _ ≤ (dimension Q : ℝ) / ((dimension Q : ℝ) + 1) *
          (((dimension Q : ℝ) / ((dimension Q : ℝ) + 1)) ^ k * mesh Q) :=
        mul_le_mul_of_nonneg_left ih hfactor
      _ = _ := by rw [pow_succ]; ring

/-- If [a complex has finitely many faces](hyp:hQ), [the meshes of its iterated
subdivisions tend to zero](goal). -/
theorem mesh_sdIterate_tendsto_zero {Q : Geometry.SimplicialComplex ℝ E}
    (hQ : Q.faces.Finite) :
    Filter.Tendsto (fun k => mesh (sdIterate Q k)) Filter.atTop (nhds 0) := by
  have hfactor : 0 ≤ (dimension Q : ℝ) / ((dimension Q : ℝ) + 1) :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hlt : (dimension Q : ℝ) / ((dimension Q : ℝ) + 1) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hfactor hlt).mul_const (mesh Q)
  apply squeeze_zero (fun k => mesh_nonneg (sdIterate_finite hQ k))
    (mesh_sdIterate_le hQ)
  simpa using hlim

end Toolkit.Foundations.Topology
