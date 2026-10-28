module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.Pointwise
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Star
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.List
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Algebra.Star.Real
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Algebra.StarSubalgebra
public import Mathlib.Topology.Bases
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Lemmas
public import Mathlib.Topology.UniformSpace.Defs

/-!
# Elementary norm estimates and generated star algebras

A countably generated closed complex star algebra is separable. The argument uses
countably many words in the generators and their adjoints, followed by separability
of their complex linear span and its closure. Neither completeness nor the C*-norm
identity is needed.

In a C*-ring, the sum of finitely many contractions with orthogonal ranges has norm
at most the square root of the number of terms: the C*-identity reduces this estimate
to the triangle inequality once all off-diagonal products vanish (cf. Davidson,
*C*-Algebras by Example*, §I.5).


For C*-algebras, see Murphy, *C*-Algebras and Operator Theory*, §3.1 and Remark 4.4.1.
-/

public section

namespace Toolkit.Foundations.Analysis.Normed

open scoped Pointwise

/-- The norm closure of the star algebra generated by
[a countable set of elements](hyp:s,hs) in a complex normed star algebra with continuous
involution [is a separable subset of that algebra](goal).

Finite words in the generators and their adjoints form a countable set. The generated
star algebra is their complex linear span, whose separability passes to its closure. -/
theorem isSeparable_topologicalClosure_starAlgebraAdjoin_of_countable
    {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℂ A]
    [StarModule ℂ A] [ContinuousStar A] (s : Set A) (hs : s.Countable) :
    TopologicalSpace.IsSeparable ((StarAlgebra.adjoin ℂ s).topologicalClosure : Set A) := by
  have ht : (s ∪ star s).Countable := by
    rw [← Set.image_star]
    exact hs.union (hs.image star)
  have hw : (Submonoid.closure (s ∪ star s) : Set A).Countable := by
    have : Countable (s ∪ star s : Set A) := ht.to_subtype
    have : Countable (FreeMonoid (s ∪ star s : Set A)) :=
      inferInstanceAs (Countable (List (s ∪ star s : Set A)))
    rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
    exact Set.countable_range _
  rw [StarSubalgebra.topologicalClosure_coe]
  have hspan := hw.isSeparable.span (R := ℂ)
  rw [← StarAlgebra.adjoin_eq_span] at hspan
  exact hspan.closure

/-- A finite sum of elements in a C*-algebra, [each with norm at most one](hyp:hnorm)
and [with the adjoint of each element times any distinct element equal to zero](hyp:horth),
[has norm at most the square root of the number of terms](goal).

The C*-identity expresses the squared norm of the sum as the norm of its adjoint
times itself. Expand this product, discard the zero off-diagonal terms, and
bound each remaining term by one using the triangle inequality and C*-identity.
Only the axioms of a non-unital C*-ring are used.
-/
theorem norm_sum_le_sqrt_card_of_star_mul_eq_zero
    {A ι : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (s : Finset ι) (a : ι → A)
    (hnorm : ∀ i ∈ s, ‖a i‖ ≤ 1)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → star (a i) * a j = 0) :
    ‖∑ i ∈ s, a i‖ ≤ Real.sqrt (s.card : ℝ) := by
  classical
  have hdiag : star (∑ i ∈ s, a i) * (∑ i ∈ s, a i) =
      ∑ i ∈ s, star (a i) * a i := by
    rw [star_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_eq_single i
      (fun j hj hji => horth i hi j hj hji.symm)
      (fun hni => (hni hi).elim)
  apply Real.le_sqrt_of_sq_le
  calc
    ‖∑ i ∈ s, a i‖ ^ 2 = ‖star (∑ i ∈ s, a i) * (∑ i ∈ s, a i)‖ := by
      rw [CStarRing.norm_star_mul_self, sq]
    _ = ‖∑ i ∈ s, star (a i) * a i‖ := congrArg norm hdiag
    _ ≤ ∑ i ∈ s, ‖star (a i) * a i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [CStarRing.norm_star_mul_self]
      simpa using mul_le_mul (hnorm i hi) (hnorm i hi) (norm_nonneg (a i)) zero_le_one
    _ = (s.card : ℝ) := by simp

/-- In a unital C*-ring, conjugating [an arbitrary element](hyp:p) by
[a unitary element](hyp:u) [moves it in norm by at most twice the element's norm
times the distance of the unitary from the identity](goal).

This is the basic step of Kadison–Kastler perturbation arguments (cf. Christensen,
*Near inclusions of C*-algebras*, Acta Math. 144 (1980), §2). The difference splits
as `(u - 1) * p * star u + p * (star u - 1)`; the triangle inequality and
submultiplicativity bound the two terms, right multiplication by a unitary preserves
the norm, and taking adjoints preserves the distance from the identity.
-/
theorem norm_unitary_mul_mul_star_sub_le
    {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    (u : unitary A) (p : A) :
    ‖(u : A) * p * star (u : A) - p‖ ≤ 2 * ‖p‖ * ‖(u : A) - 1‖ := by
  have hstar : ‖star (u : A) - 1‖ = ‖(u : A) - 1‖ := by
    simpa only [star_sub, star_one] using (norm_star ((u : A) - 1))
  have hunit : ‖((u : A) - 1) * p * star (u : A)‖ =
      ‖((u : A) - 1) * p‖ := by
    simpa only [Unitary.coe_star] using
      CStarRing.norm_mul_coe_unitary (((u : A) - 1) * p) (star u)
  calc
    ‖(u : A) * p * star (u : A) - p‖ =
        ‖((u : A) - 1) * p * star (u : A) + p * (star (u : A) - 1)‖ := by
      simp only [sub_mul, mul_sub, one_mul, mul_one, sub_add_sub_cancel]
    _ ≤ ‖((u : A) - 1) * p * star (u : A)‖ +
        ‖p * (star (u : A) - 1)‖ := norm_add_le _ _
    _ = ‖((u : A) - 1) * p‖ + ‖p * (star (u : A) - 1)‖ := by rw [hunit]
    _ ≤ ‖(u : A) - 1‖ * ‖p‖ + ‖p‖ * ‖star (u : A) - 1‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖p‖ * ‖(u : A) - 1‖ := by
      rw [hstar, mul_comm ‖(u : A) - 1‖ ‖p‖, ← two_mul, mul_assoc]



end Toolkit.Foundations.Analysis.Normed

namespace Toolkit.Foundations.Analysis.Normed

section

open scoped Topology
variable {A : Type*} [CStarAlgebra A]

/-- If [E is an orthogonal projection](hyp:hE) and [x belongs to the real
spectrum of X](hyp:hx), then [the smaller of the distances from x to zero
and to one is at most the norm distance from X to E](goal). -/
-- @node: corner_spectrum_near_projection
lemma min_norm_norm_sub_one_le_norm_sub_of_mem_spectrum (X E : A) (hE : IsStarProjection E)
    (x : ℝ) (hx : x ∈ spectrum ℝ X) :
    min ‖x‖ ‖x - 1‖ ≤ ‖X - E‖ := by
  by_contra! h
  let m := min ‖x‖ ‖x - 1‖
  have hm : 0 < m := lt_of_le_of_lt (norm_nonneg _) h
  have hn : ∀ y ∈ spectrum ℝ E, x - y ≠ 0 := by
    intro y hy
    rcases hE.isIdempotentElem.spectrum_subset ℝ hy with hy | hy
    · have hy : y = 0 := hy
      subst y
      have : 0 < ‖x‖ := hm.trans_le (min_le_left _ _)
      simpa only [sub_zero] using norm_pos_iff.mp this
    · have hy : y = 1 := hy
      subst y
      exact norm_pos_iff.mp (hm.trans_le (min_le_right _ _))
  have hf : ContinuousOn (fun y : ℝ => (x - y)⁻¹) (spectrum ℝ E) := by
    fun_prop (disch := assumption)
  let v := cfc (fun y : ℝ => (x - y)⁻¹) E
  have hv : ‖v‖ ≤ m⁻¹ := by
    apply norm_cfc_le (le_of_lt (inv_pos.mpr hm))
    intro y hy
    rw [norm_inv]
    apply inv_anti₀ hm
    rcases hE.isIdempotentElem.spectrum_subset ℝ hy with hy | hy
    · have hy : y = 0 := hy
      simpa [hy, m] using min_le_left ‖x‖ ‖x - 1‖
    · have hy : y = 1 := hy
      simpa [hy, m] using min_le_right ‖x‖ ‖x - 1‖
  have ha : cfc (fun y : ℝ => x - y) E = algebraMap ℝ A x - E := by
    rw [cfc_sub (fun _ : ℝ => x) (fun y : ℝ => y) E,
      cfc_const x E hE.isSelfAdjoint, cfc_id' ℝ E hE.isSelfAdjoint]
  have hav : (algebraMap ℝ A x - E) * v = 1 := by
    rw [← ha, ← cfc_mul _ _ E (by fun_prop) hf]
    convert cfc_const_one ℝ E using 1
    apply cfc_congr
    intro y hy
    exact mul_inv_cancel₀ (hn y hy)
  have hva : v * (algebraMap ℝ A x - E) = 1 := by
    rw [← ha, ← cfc_mul _ _ E hf (by fun_prop)]
    convert cfc_const_one ℝ E using 1
    apply cfc_congr
    intro y hy
    exact inv_mul_cancel₀ (hn y hy)
  let u : Aˣ := ⟨algebraMap ℝ A x - E, v, hav, hva⟩
  have hsmall : ‖v * (E - X)‖ < 1 := by
    calc
      _ ≤ ‖v‖ * ‖E - X‖ := norm_mul_le _ _
      _ ≤ m⁻¹ * ‖X - E‖ := by
        rw [norm_sub_rev E X]
        exact mul_le_mul_of_nonneg_right hv (norm_nonneg _)
      _ < m⁻¹ * m := mul_lt_mul_of_pos_left h (inv_pos.mpr hm)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hm)
  have hw : IsUnit (1 + v * (E - X)) := by
    simpa only [sub_neg_eq_add] using
      isUnit_one_sub_of_norm_lt_one (by simpa only [norm_neg] using hsmall :
        ‖-(v * (E - X))‖ < 1)
  have hu := u.isUnit.mul hw
  have heq : (u : A) * (1 + v * (E - X)) = algebraMap ℝ A x - X := by
    change (algebraMap ℝ A x - E) * (1 + v * (E - X)) = _
    rw [mul_add, mul_one, ← mul_assoc, hav, one_mul]
    abel
  rw [heq] at hu
  exact hx hu

end

end Toolkit.Foundations.Analysis.Normed

namespace Toolkit.Foundations.Analysis.Normed

section

open Filter
open scoped Topology Matrix.Norms.Operator

-- @node: unitary_commutator_norm_eq
/-- In [a normed ring B with an adjoint satisfying the C-star norm identity](hyp:B), take
[elements U and V](hyp:U,V). If [U is unitary](hyp:hU) and [V is unitary](hyp:hV), then
[the norm of their multiplicative commutator minus the identity equals the norm of UV minus VU](goal). -/
lemma norm_mul_mul_star_mul_star_sub_one_eq_norm_commutator
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B]
    (U V : B) (hU : U ∈ unitary B) (hV : V ∈ unitary B) :
    ‖U * V * star U * star V - 1‖ = ‖U * V - V * U‖ := by
  have hc : V * U * star U * star V = 1 := by
    rw [mul_assoc V U (star U), Unitary.mul_star_self_of_mem hU, mul_one,
      Unitary.mul_star_self_of_mem hV]
  have ht : U * V * star U * star V - 1 = (U * V - V * U) * star U * star V := by
    rw [sub_mul, sub_mul, hc]
  rw [ht, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hV),
    CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU)]

end

end Toolkit.Foundations.Analysis.Normed

namespace Toolkit.Foundations.Analysis.Normed

section

open scoped Topology Matrix.Norms.Operator

-- @node: unitary_product_difference_norm_le
/-- In [a normed ring B with an adjoint satisfying the C-star norm identity](hyp:B), take
[elements a, b, c, and d](hyp:a,b,c,d). If [a is unitary](hyp:ha) and [d is unitary](hyp:hd),
then [the norm of ab minus cd is at most the norm of a minus c plus the norm of b minus d](goal). -/
lemma norm_mul_sub_mul_le_of_mem_unitary
    {B : Type*} [NormedRing B] [StarRing B] [CStarRing B]
    (a b c d : B) (ha : a ∈ unitary B) (hd : d ∈ unitary B) :
    ‖a * b - c * d‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  have ht : a * b - c * d = (a - c) * d + a * (b - d) := by noncomm_ring
  rw [ht]
  exact (norm_add_le _ _).trans_eq (by
    rw [CStarRing.norm_mul_mem_unitary _ hd, CStarRing.norm_mem_unitary_mul _ ha])

end

end Toolkit.Foundations.Analysis.Normed


namespace Toolkit.Foundations.Analysis.Normed

/-- In a normed ring, if [an element U has norm at most one](hyp:hU), then for any element X
and any natural number n, [the norm of the commutator of the nth power of U with X is at most
n times the norm of the commutator of U with X](goal).

This is the standard telescoping estimate (cf. Davidson, *C*-Algebras by Example*, §I.3):
the commutator of the next power splits as a power of U times the basic commutator plus the
previous commutator times U, and submultiplicativity bounds both terms. Multiplication by
every power of the contraction decreases norms, proved directly by induction so that no
norm-one assumption on the identity is needed.
-/
theorem norm_pow_mul_sub_mul_pow_le_mul_norm_commutator
    {B : Type*} [NormedRing B] (U X : B) (hU : ‖U‖ ≤ 1) (n : ℕ) :
    ‖U ^ n * X - X * U ^ n‖ ≤ (n : ℝ) * ‖U * X - X * U‖ := by
  have hpow (k : ℕ) (Y : B) : ‖U ^ k * Y‖ ≤ ‖Y‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        ‖U ^ (k + 1) * Y‖ = ‖U * (U ^ k * Y)‖ := by
          rw [pow_succ', mul_assoc]
        _ ≤ ‖U‖ * ‖U ^ k * Y‖ := norm_mul_le _ _
        _ ≤ 1 * ‖U ^ k * Y‖ := mul_le_mul_of_nonneg_right hU (norm_nonneg _)
        _ ≤ ‖Y‖ := by simpa using ih
  induction n with
  | zero => simp
  | succ n ih =>
    have hrec : U ^ (n + 1) * X - X * U ^ (n + 1) =
        U ^ n * (U * X - X * U) + (U ^ n * X - X * U ^ n) * U := by
      simp [pow_succ, mul_sub, sub_mul, mul_assoc]
    calc
      ‖U ^ (n + 1) * X - X * U ^ (n + 1)‖ =
          ‖U ^ n * (U * X - X * U) + (U ^ n * X - X * U ^ n) * U‖ := by
        rw [hrec]
      _ ≤ ‖U ^ n * (U * X - X * U)‖ + ‖(U ^ n * X - X * U ^ n) * U‖ :=
        norm_add_le _ _
      _ ≤ ‖U * X - X * U‖ + ‖U ^ n * X - X * U ^ n‖ := by
        apply add_le_add (hpow n _)
        calc
          ‖(U ^ n * X - X * U ^ n) * U‖ ≤ ‖U ^ n * X - X * U ^ n‖ * ‖U‖ :=
            norm_mul_le _ _
          _ ≤ ‖U ^ n * X - X * U ^ n‖ * 1 :=
            mul_le_mul_of_nonneg_left hU (norm_nonneg _)
          _ = ‖U ^ n * X - X * U ^ n‖ := mul_one _
      _ ≤ ‖U * X - X * U‖ + (n : ℝ) * ‖U * X - X * U‖ :=
        add_le_add le_rfl ih
      _ = ((n + 1 : ℕ) : ℝ) * ‖U * X - X * U‖ := by
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

end Toolkit.Foundations.Analysis.Normed
