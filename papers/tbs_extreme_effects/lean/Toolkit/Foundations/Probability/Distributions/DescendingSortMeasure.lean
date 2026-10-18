module

public import Batteries.Logic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Logic.Pairwise
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.AEDisjoint
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs
public import StatLean.Bayesian.Sufficiency.Factorization
public import Toolkit.Foundations.Probability.Distributions.DescendingOrderStatistics

/-!
# Sorting symmetric densities into a descending chamber

Sorting folds the permutation chambers onto the canonical descending chamber.
Distinct chambers overlap only on equal-coordinate hyperplanes, which are null
for Lebesgue measure. The resulting density acquires the sample-size factorial.
This module is independent of the exponential distribution.

The main results are measurability of the descending sort
(`measurable_sortDescending`), the image of Lebesgue measure under sorting
(`map_sortDescending_volume`), and the law of the order statistics of a sample with a
permutation-symmetric joint density (`map_sortDescending_withDensity`).
-/

@[expose] public section

namespace Toolkit.Foundations.Probability.Distributions

open MeasureTheory Function

noncomputable section

/-- For [a sample size](hyp:n) and [a coordinate permutation](hyp:σ), [the descending permutation
chamber](goal) consists of vectors that become nonincreasing under that permutation. -/
def descendingChamber (n : ℕ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {x | Antitone (x ∘ σ)}

/-- [Sorting a finite real vector into descending order is measurable](goal). -/
theorem measurable_sortDescending {n : ℕ} :
    Measurable (sortDescending (n := n)) := by
  -- Use finitely many measurable order chambers and coordinate permutations;
  -- a measurable sorting permutation is not required.
  classical
  intro s hs
  have hpre : sortDescending ⁻¹' s =
      ⋃ σ : Equiv.Perm (Fin n), descendingChamber n σ ∩
        (fun x : Fin n → ℝ => x ∘ σ) ⁻¹' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      refine ⟨Fin.revPerm.trans (Tuple.sort x), antitone_sortDescending x, hx⟩
    · rintro ⟨σ, hσ, hx⟩
      rwa [sortDescending_eq_comp_of_antitone x σ hσ]
  rw [hpre]
  apply MeasurableSet.iUnion
  intro σ
  have hc : Continuous (fun x : Fin n → ℝ => x ∘ σ) :=
    continuous_pi fun i => continuous_apply (σ i)
  exact (isClosed_antitone.preimage hc).measurableSet.inter (hc.measurable hs)

/-- For [a sample size](hyp:n) and [a coordinate permutation](hyp:σ), [the descending permutation
chamber is measurable](goal). -/
theorem measurableSet_descendingChamber (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (descendingChamber n σ) := by
  have hcont : Continuous (fun x : Fin n → ℝ => x ∘ σ) :=
    continuous_pi fun i => continuous_apply (σ i)
  exact (isClosed_antitone.preimage hcont).measurableSet

/-- For [two distinct ranks](hyp:hij), [the real vectors whose coordinates at those ranks coincide
have zero Lebesgue measure](goal). -/
theorem volume_equal_coordinate_zero {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    volume {x : Fin n → ℝ | x i = x j} = 0 := by
  -- This is the kernel of the nonzero linear functional proj i - proj j.
  -- Apply Measure.addHaar_submodule; no dimension-positive assumption is needed.
  classical
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
  have hker : L.ker ≠ ⊤ := by
    intro h
    have hx : (Pi.single i (1 : ℝ)) ∈ L.ker := by rw [h]; trivial
    have hji : j ≠ i := Ne.symm hij
    simp [LinearMap.mem_ker, L, hji] at hx
  have hset : {x : Fin n → ℝ | x i = x j} = (L.ker : Set (Fin n → ℝ)) := by
    ext x
    simp [LinearMap.mem_ker, L, sub_eq_zero]
  rw [hset]
  exact Measure.addHaar_submodule volume L.ker hker

/-- For [a sample size](hyp:n), [Lebesgue measure is the sum of its restrictions to all descending
permutation chambers](goal). -/
theorem volume_descendingChamber_decomposition (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) =
      ∑ σ : Equiv.Perm (Fin n), volume.restrict (descendingChamber n σ) := by
  -- Chambers cover all vectors (Tuple.sort followed by reversal). Their
  -- intersections are contained in equal-coordinate faces: use unique_antitone.
  -- Finish with Measure.restrict_iUnion_ae and Measure.sum_fintype.
  classical
  have hcover : (⋃ σ : Equiv.Perm (Fin n), descendingChamber n σ) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨Fin.revPerm.trans (Tuple.sort x), antitone_sortDescending x⟩
  have hd : Pairwise (AEDisjoint (volume : Measure (Fin n → ℝ)) on
      descendingChamber n) := by
    intro σ τ hστ
    obtain ⟨k, hk⟩ : ∃ k, σ k ≠ τ k := by
      by_contra h
      apply hστ
      apply Equiv.ext
      intro k
      exact Classical.not_not.mp (fun hk => h ⟨k, hk⟩)
    change volume (descendingChamber n σ ∩ descendingChamber n τ) = 0
    apply measure_mono_null (t := {x : Fin n → ℝ | x (σ k) = x (τ k)})
    · intro x hx
      exact congrFun (Tuple.unique_antitone hx.1 hx.2) k
    · exact volume_equal_coordinate_zero (σ k) (τ k) hk
  have h := Measure.restrict_iUnion_ae hd
    (fun σ => (measurableSet_descendingChamber n σ).nullMeasurableSet)
  rw [hcover, Measure.restrict_univ, Measure.sum_fintype] at h
  exact h

/-- For [a sample size](hyp:n) and [a coordinate permutation](hyp:σ), [sorting the Lebesgue
measure restricted to that chamber yields the restriction to the canonical descending
chamber](goal). -/
theorem map_sortDescending_restrict_descendingChamber (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (volume.restrict (descendingChamber n σ)).map sortDescending =
      volume.restrict {x : Fin n → ℝ | Antitone x} := by
  -- On this chamber, use Tuple.unique_antitone to replace sorting by x ∘ σ.
  -- volume_measurePreserving_piCongrLeft supplies the coordinate-permutation law.
  classical
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => x ∘ σ
  have hg : Measurable g := measurable_pi_lambda _ fun i => measurable_pi_apply (σ i)
  have hmp : MeasurePreserving g volume volume := by
    simpa [g, Function.comp_def, MeasurableEquiv.piCongrLeft,
      Equiv.piCongrLeft, Equiv.piCongrLeft'] using
      (volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm)
  have hanti : MeasurableSet {x : Fin n → ℝ | Antitone x} :=
    isClosed_antitone.measurableSet
  have heq : sortDescending =ᵐ[volume.restrict (descendingChamber n σ)] g := by
    filter_upwards [ae_restrict_mem (measurableSet_descendingChamber n σ)] with x hx
    exact sortDescending_eq_comp_of_antitone x σ hx
  rw [Measure.map_congr heq]
  change (volume.restrict (g ⁻¹' {x : Fin n → ℝ | Antitone x})).map g = _
  rw [← Measure.restrict_map hg hanti, hmp.map_eq]

/-- For [a sample size](hyp:n), [sorting Lebesgue measure gives factorial times Lebesgue measure
on the descending chamber](goal). -/
theorem map_sortDescending_volume (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).map sortDescending =
      (n.factorial : ENNReal) • volume.restrict {x : Fin n → ℝ | Antitone x} := by
  -- Map the chamber decomposition termwise, then use Fintype.card_perm.
  classical
  conv_lhs => rw [volume_descendingChamber_decomposition n]
  rw [Measure.map_finset_sum' measurable_sortDescending.aemeasurable]
  simp only [map_sortDescending_restrict_descendingChamber]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  ext s hs
  simp [smul_eq_mul]

/-- If [a nonnegative extended-real density on finite real vectors](hyp:f)
[is measurable](hyp:hf) and [unchanged by coordinate permutations](hyp:hsymm), [sorting its
Lebesgue-density measure multiplies the density on the descending chamber by the sample-size
factorial](goal). -/
theorem map_sortDescending_withDensity {n : ℕ} (f : (Fin n → ℝ) → ENNReal)
    (hf : Measurable f)
    (hsymm : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ), f (x ∘ σ) = f x) :
    (volume.withDensity f).map sortDescending =
      (n.factorial : ENNReal) •
        ((volume.restrict {x : Fin n → ℝ | Antitone x}).withDensity f) := by
  -- First derive f ∘ sortDescending = f using the sorting permutation.
  -- Transport a density pulled back through a measurable map, then use
  -- map_sortDescending_volume. ENNReal-valued densities may be infinite.
  have hinv : (fun x => f (sortDescending x)) = f := by
    funext x
    exact hsymm (Fin.revPerm.trans (Tuple.sort x)) x
  calc
    (volume.withDensity f).map sortDescending =
        (volume.withDensity (fun x => f (sortDescending x))).map sortDescending := by
      rw [hinv]
    _ = (volume.map sortDescending).withDensity f :=
      StatLean.Bayesian.map_withDensity_comp measurable_sortDescending hf volume
    _ = _ := by rw [map_sortDescending_volume, withDensity_smul_measure]

end
end Toolkit.Foundations.Probability.Distributions
