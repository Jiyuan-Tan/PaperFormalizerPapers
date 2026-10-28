module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Core

/-!
# Signs of coefficients of real-rooted polynomials

A real polynomial with positive leading coefficient and only real roots has
nonnegative coefficients exactly when every root is nonpositive (the root-sign
half of Descartes' rule for real-rooted polynomials). This is the univariate
algebraic ingredient of the description of a closed hyperbolicity cone by the
signs of directional derivatives.
-/

public section

namespace Toolkit.Foundations.Algebra

/-- If [a real polynomial factors completely over the reals](hyp:hsplit), has
[positive leading coefficient](hyp:hlc), and [every real root is nonpositive](hyp:hroots),
then [all its coefficients are nonnegative](goal). -/
theorem coeff_nonneg_of_roots_nonpos (q : Polynomial ℝ)
    (hsplit : q.Splits) (hlc : 0 < q.leadingCoeff)
    (hroots : ∀ r : ℝ, q.IsRoot r → r ≤ 0) :
    ∀ i : ℕ, 0 ≤ q.coeff i := by
  classical
  have hmul (p t : Polynomial ℝ)
      (hp : ∀ i, 0 ≤ p.coeff i) (ht : ∀ i, 0 ≤ t.coeff i) :
      ∀ i, 0 ≤ (p * t).coeff i := by
    intro i
    rw [Polynomial.coeff_mul]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hp j.1) (ht j.2)
  have hprod : ∀ (s : Multiset ℝ), (∀ r ∈ s, r ≤ 0) →
      ∀ i, 0 ≤ (s.map (Polynomial.X - Polynomial.C ·)).prod.coeff i := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
        intro _ i
        simp only [Multiset.map_zero, Multiset.prod_zero, Polynomial.coeff_one]
        split <;> positivity
    | @cons r s ih =>
        intro hs
        rw [Multiset.map_cons, Multiset.prod_cons]
        apply hmul
        · intro i
          rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
          have hr := hs r (Multiset.mem_cons_self r s)
          split <;> split <;> simp_all
        · exact ih (fun t ht => hs t (Multiset.mem_cons_of_mem ht))
  have hp := hprod q.roots (fun r hr => hroots r (Polynomial.isRoot_of_mem_roots hr))
  intro i
  rw [hsplit.eq_prod_roots, Polynomial.coeff_C_mul]
  exact mul_nonneg hlc.le (hp i)

/-- If [a real polynomial is not the zero polynomial](hyp:hq) and has
[nonnegative coefficients](hyp:hcoeff), then [every real root is nonpositive](goal). -/
theorem roots_nonpos_of_coeff_nonneg (q : Polynomial ℝ) (hq : q ≠ 0)
    (hcoeff : ∀ i : ℕ, 0 ≤ q.coeff i) :
    ∀ r : ℝ, q.IsRoot r → r ≤ 0 := by
  classical
  intro r hr
  by_contra hn
  have hpos : 0 < r := lt_of_not_ge hn
  have hlc : 0 < q.coeff q.natDegree :=
    lt_of_le_of_ne (hcoeff _) (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr hq))
  have heval : 0 < q.eval r := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum]
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (hcoeff i) (pow_nonneg hpos.le i)
    · exact ⟨q.natDegree, Polynomial.mem_support_iff.mpr (ne_of_gt hlc),
        mul_pos hlc (pow_pos hpos _)⟩
  exact (ne_of_gt heval) hr

/-- For [a real polynomial that factors completely over the reals](hyp:hsplit)
with [positive leading coefficient](hyp:hlc),
[all real roots are nonpositive exactly when every coefficient is nonnegative](goal). -/
theorem roots_nonpos_iff_coeff_nonneg (q : Polynomial ℝ)
    (hsplit : q.Splits) (hlc : 0 < q.leadingCoeff) :
    (∀ r : ℝ, q.IsRoot r → r ≤ 0) ↔ ∀ i : ℕ, 0 ≤ q.coeff i := by
  exact ⟨coeff_nonneg_of_roots_nonpos q hsplit hlc,
    roots_nonpos_of_coeff_nonneg q (fun h => by simpa [h] using hlc.ne')⟩

end Toolkit.Foundations.Algebra
