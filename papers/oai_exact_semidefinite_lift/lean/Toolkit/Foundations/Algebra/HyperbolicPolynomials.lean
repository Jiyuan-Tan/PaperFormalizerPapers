module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Toolkit.Foundations.Algebra.PolynomialCoeffSigns

/-!
# Hyperbolic polynomials and the signs of Renegar derivatives

A function on a finite-dimensional real vector space is a homogeneous polynomial
of degree n when it is given, in basis coordinates, by a homogeneous multivariate
polynomial of degree n. It is hyperbolic in a direction e when it is positive at e
and its restriction to every affine line in direction e factors completely over the
reals. Eigenvalues of a vector x are the roots, with multiplicity, of the
characteristic polynomial λ ↦ p(λ • e - x); the closed hyperbolicity cone requires
every eigenvalue to be nonnegative. The Renegar derivatives are the repeated
directional derivatives of p along e.

Main results:
* `iteratedDirectionalDerivative_eq_esymm_eigenvalues`: the i-th Renegar derivative
  equals i! · p(e) · σ_{n-i}(eigenvalues) (Renegar, Proposition 18).
* `mem_hyperbolicityCone_iff_forall_iteratedDerivative_nonneg`: the closed cone is
  the set where the Renegar derivatives of orders 0, …, n − 1 are nonnegative
  (Renegar, Theorem 20, in derivative form).

The standard instance is the determinant on symmetric matrices with a positive
definite direction, whose closed cone is the positive semidefinite cone.

Reference: J. Renegar, *Hyperbolic programs, and their derivative relaxations*,
Foundations of Computational Mathematics 6 (2006), 59–79, §5. Proposition 18 and
Theorem 20 refer to the March 2004 preprint, downloaded from
https://optimization-online.org/wp-content/uploads/2004/03/844.pdf.
Its SHA-256 is 246bb41321a8d82c1838a6496ccdc336f1e638a6947a868078262ff1fe48e1a4.
Journal-version numbering has not been checked. No determinant-specific
assumptions, eigenvalue ordering, or choice of an inner product is needed.
-/

@[expose] public section

namespace Toolkit.Foundations.Algebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- For [a function on a finite-dimensional real vector space](hyp:p,E) and
[a natural-number degree](hyp:n), [being a homogeneous polynomial](goal) means
that it has [a multivariate polynomial representative homogeneous of that degree](step:1)
whose [evaluation in basis coordinates gives the function at every vector](step:2). -/
def IsHomogeneousPolynomial (p : E → ℝ) (n : ℕ) : Prop :=
  ∃ q : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ,
    q.IsHomogeneous n ∧ ∀ x : E, q.eval ((Module.finBasis ℝ E).repr x) = p x

/-- For [a multivariate real polynomial](hyp:q) and
[a direction and a base point in its coordinate space](hyp:e,x),
[the polynomial on their affine line](goal) substitutes each coordinate by
the corresponding base coordinate plus the direction coordinate times the variable. -/
noncomputable def mvPolynomialOnLine {ι : Type*} (q : MvPolynomial ι ℝ)
    (e x : ι → ℝ) : Polynomial ℝ :=
  q.eval₂ Polynomial.C (fun j => Polynomial.C (x j) +
    Polynomial.C (e j) * Polynomial.X)

/-- At [any real parameter](hyp:t), [evaluating the line restriction equals
evaluating the original polynomial at the corresponding affine point](goal). -/
theorem eval_mvPolynomialOnLine {ι : Type*} (q : MvPolynomial ι ℝ)
    (e x : ι → ℝ) (t : ℝ) :
    (mvPolynomialOnLine q e x).eval t = q.eval (fun j => x j + t * e j) := by
  -- Compose the evaluation homomorphism with the multivariate substitution.
  change (Polynomial.evalRingHom t) (q.eval₂ Polynomial.C _) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℝ := by
    ext r
    simp
  rw [hc, MvPolynomial.eval₂_id]
  apply congrArg (fun v : ι → ℝ => q.eval v)
  funext j
  change Polynomial.eval t (Polynomial.C (x j) +
    Polynomial.C (e j) * Polynomial.X) = x j + t * e j
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, mul_comm]

/-- If [a multivariate polynomial is homogeneous of degree n](hyp:hq),
then [its restriction to any affine line has degree at most n](goal). -/
theorem natDegree_mvPolynomialOnLine_le {ι : Type*} (q : MvPolynomial ι ℝ)
    (e x : ι → ℝ) (n : ℕ) (hq : q.IsHomogeneous n) :
    (mvPolynomialOnLine q e x).natDegree ≤ n := by
  -- Expand over q.support. A monomial substitutes to a product of powers of
  -- linear polynomials, of degree at most the sum of its exponents (= n).
  classical
  have hlin (j : ι) :
      (Polynomial.C (x j) + Polynomial.C (e j) * Polynomial.X).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  rw [mvPolynomialOnLine, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [hq.degree_eq_sum_deg_support hd]
  refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  simpa using Polynomial.natDegree_pow_le_of_le (d j) (hlin j)

/-- If [a multivariate polynomial is homogeneous of degree n](hyp:hq),
then [the degree-n coefficient of its line restriction is its value at the direction](goal). -/
theorem coeff_mvPolynomialOnLine_degree {ι : Type*} (q : MvPolynomial ι ℝ)
    (e x : ι → ℝ) (n : ℕ) (hq : q.IsHomogeneous n) :
    (mvPolynomialOnLine q e x).coeff n = q.eval e := by
  -- The top coefficient of each substituted monomial is the product of the
  -- direction coordinates, with the same exponents as the original monomial.
  classical
  let L (j : ι) : Polynomial ℝ :=
    Polynomial.C (x j) + Polynomial.C (e j) * Polynomial.X
  have hlin (j : ι) : (L j).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  have hpow (j : ι) (k : ℕ) : (L j ^ k).natDegree ≤ k := by
    simpa using Polynomial.natDegree_pow_le_of_le k (hlin j)
  have hprod (d : ι →₀ ℕ) (s : Finset ι) :
      (∏ j ∈ s, L j ^ d j).natDegree ≤ ∑ j ∈ s, d j ∧
      (∏ j ∈ s, L j ^ d j).coeff (∑ j ∈ s, d j) = ∏ j ∈ s, e j ^ d j := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.prod_insert hj]
      constructor
      · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hpow j _) ih.1)
      · rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hpow j _) ih.1, ih.2]
        congr 1
        simpa [L] using (Polynomial.coeff_pow_of_natDegree_le (m := d j) (hlin j))
  rw [mvPolynomialOnLine, MvPolynomial.eval₂_eq, MvPolynomial.eval_eq]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hq.degree_eq_sum_deg_support hd]
  exact congrArg (q.coeff d * ·) (hprod d d.support).2

/-- For [a real-valued function on a real vector space](hyp:p,E) and
[a direction and base point](hyp:e,x), [its polynomial on the affine line](goal)
is [the unique polynomial giving its values along that line, when one exists](step:1),
and [zero when no such polynomial exists](step:2). -/
noncomputable def polynomialOnLine (p : E → ℝ) (e x : E) : Polynomial ℝ := by
  classical
  exact if h : ∃ q : Polynomial ℝ, ∀ t : ℝ, q.eval t = p (x + t • e) then h.choose else 0

/-- If [a function is a homogeneous polynomial](hyp:hp),
then [on every affine line it agrees with a univariate polynomial whose degree
is at most its homogeneous degree and whose top coefficient is its value at the direction](goal). -/
theorem exists_polynomialOnLine {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) :
    ∃ q : Polynomial ℝ, (∀ t : ℝ, q.eval t = p (x + t • e)) ∧
      q.natDegree ≤ n ∧ q.coeff n = p e := by
  -- Use the homogeneous representative in hp and the three preceding lemmas;
  -- the basis coordinate map preserves addition and real scalar multiplication.
  obtain ⟨q, hq, hval⟩ := hp
  refine ⟨mvPolynomialOnLine q ((Module.finBasis ℝ E).repr e)
    ((Module.finBasis ℝ E).repr x), ?_,
    natDegree_mvPolynomialOnLine_le q _ _ n hq, ?_⟩
  · intro t
    rw [eval_mvPolynomialOnLine]
    have hcoord : (fun j => ((Module.finBasis ℝ E).repr x) j +
        t * ((Module.finBasis ℝ E).repr e) j) =
        fun j => ((Module.finBasis ℝ E).repr (x + t • e)) j := by
      funext j
      simp
    rw [hcoord]
    exact hval (x + t • e)
  · rw [coeff_mvPolynomialOnLine_degree q _ _ n hq, hval]

/-- If [a function is a homogeneous polynomial](hyp:hp),
then [its chosen line polynomial evaluates to the function at each affine point](goal). -/
theorem eval_polynomialOnLine {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) (t : ℝ) :
    (polynomialOnLine p e x).eval t = p (x + t • e) := by
  obtain ⟨q, hq, _⟩ := exists_polynomialOnLine hp e x
  have h : ∃ q : Polynomial ℝ, ∀ t : ℝ, q.eval t = p (x + t • e) := ⟨q, hq⟩
  simpa only [polynomialOnLine, dif_pos h] using h.choose_spec t

/-- If [a function is a homogeneous polynomial of degree n](hyp:hp),
then [its line polynomial has degree at most n](goal). -/
theorem natDegree_polynomialOnLine_le {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) :
    (polynomialOnLine p e x).natDegree ≤ n := by
  -- Uniqueness of polynomial evaluation identifies polynomialOnLine with the
  -- bounded-degree witness in exists_polynomialOnLine.
  obtain ⟨q, hval, hdeg, _⟩ := exists_polynomialOnLine hp e x
  have hq : polynomialOnLine p e x = q := Polynomial.funext fun t =>
    (eval_polynomialOnLine hp e x t).trans (hval t).symm
  rw [hq]
  exact hdeg

/-- If [a function is a homogeneous polynomial of degree n](hyp:hp),
then [the degree-n coefficient of its line polynomial is its value at the direction](goal). -/
theorem coeff_polynomialOnLine_degree {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) :
    (polynomialOnLine p e x).coeff n = p e := by
  obtain ⟨q, hval, _, hcoeff⟩ := exists_polynomialOnLine hp e x
  have hq : polynomialOnLine p e x = q := Polynomial.funext fun t =>
    (eval_polynomialOnLine hp e x t).trans (hval t).symm
  rw [hq]
  exact hcoeff

/-- If [a function is a homogeneous polynomial of degree n](hyp:hp),
then [scaling its argument by any real scalar scales its value by that scalar to power n](goal). -/
theorem IsHomogeneousPolynomial.map_smul {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (a : ℝ) (x : E) :
    p (a • x) = a ^ n * p x := by
  classical
  obtain ⟨q, hq, hval⟩ := hp
  rw [← hval (a • x), ← hval x, MvPolynomial.eval_eq,
    MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, mul_pow,
    Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, ← hq.degree_eq_sum_deg_support hd]
  ring


/-- For [a real-valued function on a finite-dimensional real vector space](hyp:p,E)
and [a fixed direction](hyp:e), [its sequence of Renegar derivatives](goal)
starts with [the function itself](step:1) and continues by
[differentiating the previous function along that direction at each point](step:2). -/
noncomputable def iteratedDirectionalDerivative (p : E → ℝ) (e : E) : ℕ → E → ℝ
  | 0 => p
  | i + 1 => fun x => deriv (fun t : ℝ => iteratedDirectionalDerivative p e i (x + t • e)) 0

/-- If [a function is a homogeneous polynomial](hyp:hp), then
[shifting the base point along its direction translates the variable
of its line polynomial](goal). -/
theorem polynomialOnLine_add_smul {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) (s : ℝ) :
    polynomialOnLine p e (x + s • e) =
      (polynomialOnLine p e x).comp (Polynomial.X + Polynomial.C s) := by
  -- Apply Polynomial.funext, eval_polynomialOnLine, and add_smul.
  apply Polynomial.funext
  intro t
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, eval_polynomialOnLine hp]
  rw [add_smul]
  simp [add_assoc, add_comm]

/-- If [a function is a homogeneous polynomial](hyp:hp),
then [every repeated directional derivative along a line equals the corresponding
formal derivative of the line polynomial evaluated at that parameter](goal). -/
theorem iteratedDirectionalDerivative_onLine {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) (i : ℕ) (t : ℝ) :
    iteratedDirectionalDerivative p e i (x + t • e) =
      ((Polynomial.derivative^[i]) (polynomialOnLine p e x)).eval t := by
  -- Induct on i, generalizing t. In the successor case rewrite the function of
  -- the differentiation parameter via x + t•e + s•e = x + (t+s)•e;
  -- use Polynomial.hasDerivAt composed with the affine map s ↦ t+s.
  -- Mathlib.Analysis.Calculus.Deriv.Polynomial already supplies hasDerivAt;
  -- keep x fixed in the induction and generalize t, so the induction hypothesis
  -- rewrites the whole function under deriv. No differentiability assumption
  -- on p or on the previous directional derivative needs to be added.
  induction i generalizing t with
  | zero =>
      simpa only [iteratedDirectionalDerivative, Function.iterate_zero, id_eq] using
        (eval_polynomialOnLine hp e x t).symm
  | succ i ih =>
      have hline :
          (fun s : ℝ => iteratedDirectionalDerivative p e i (x + t • e + s • e)) =
            (fun s : ℝ =>
              ((Polynomial.derivative^[i]) (polynomialOnLine p e x)).eval (t + s)) := by
        funext s
        rw [show x + t • e + s • e = x + (t + s) • e by
          rw [add_smul, add_assoc]]
        exact ih (t + s)
      change deriv (fun s : ℝ =>
        iteratedDirectionalDerivative p e i (x + t • e + s • e)) 0 = _
      rw [hline, Function.iterate_succ_apply']
      simpa only [Function.comp_def, id_eq, add_zero, mul_one] using
        ((((Polynomial.derivative^[i]) (polynomialOnLine p e x)).hasDerivAt (t + 0)).comp
          0 ((hasDerivAt_id (0 : ℝ)).const_add t)).deriv

/-- If [a function is a homogeneous polynomial](hyp:hp),
then [its i-th directional derivative at a point equals i factorial times
the coefficient of degree i in its line polynomial](goal). -/
theorem iteratedDirectionalDerivative_eq_factorial_mul_coeff {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) (i : ℕ) :
    iteratedDirectionalDerivative p e i x =
      (Nat.factorial i : ℝ) * (polynomialOnLine p e x).coeff i := by
  -- Specialize iteratedDirectionalDerivative_onLine to t = 0 and use
  -- Polynomial.coeff_iterate_derivative at coefficient zero.
  have h := iteratedDirectionalDerivative_onLine hp e x i 0
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative] at h
  simpa [Nat.descFactorial_self, nsmul_eq_mul] using h


/-- For [a real-valued function on a finite-dimensional real vector space](hyp:p,E)
and [a direction](hyp:e), [hyperbolicity in that direction](goal) requires
[a positive value at the direction](step:1) and
[complete factorization over the reals of every line polynomial in that direction](step:2).

Polynomiality and homogeneity are separate hypotheses of the theorems below. -/
def IsHyperbolic (p : E → ℝ) (e : E) : Prop :=
  0 < p e ∧ ∀ x : E, (polynomialOnLine p e x).Splits

/-- For [a function on a finite-dimensional real vector space](hyp:p,E),
[a direction](hyp:e), and [a vector](hyp:x), [the characteristic polynomial](goal)
is its line polynomial based at the negative of that vector. -/
noncomputable def characteristicPolynomial (p : E → ℝ) (e x : E) : Polynomial ℝ :=
  polynomialOnLine p e (-x)

/-- For [a function on a finite-dimensional real vector space](hyp:p,E),
[a direction](hyp:e), and [a vector](hyp:x), [the multiset of eigenvalues](goal)
consists of the real roots of its characteristic polynomial, counted with multiplicity. -/
noncomputable def eigenvalues (p : E → ℝ) (e x : E) : Multiset ℝ :=
  (characteristicPolynomial p e x).roots

/-- For [a function on a finite-dimensional real vector space](hyp:p,E)
and [a direction](hyp:e), [the closed hyperbolicity cone](goal) consists of the vectors
whose characteristic polynomial has no negative real root. -/
def hyperbolicityCone (p : E → ℝ) (e : E) : Set E :=
  {x | ∀ r : ℝ, (characteristicPolynomial p e x).IsRoot r → 0 ≤ r}

/-- If [a function is a homogeneous polynomial](hyp:hp),
then [its characteristic polynomial at a real parameter equals its value
at that parameter times the direction minus the vector](goal). -/
theorem eval_characteristicPolynomial {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) (t : ℝ) :
    (characteristicPolynomial p e x).eval t = p (t • e - x) := by
  simpa [characteristicPolynomial, sub_eq_add_neg, add_comm] using
    eval_polynomialOnLine hp e (-x) t

/-- If [a function is a homogeneous polynomial](hyp:hp),
then [a real number is a characteristic root exactly when its negative is
a root of the line polynomial based at the vector](goal). -/
theorem isRoot_characteristicPolynomial_iff {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) (r : ℝ) :
    (characteristicPolynomial p e x).IsRoot r ↔
      (polynomialOnLine p e x).IsRoot (-r) := by
  -- Use p (-(x + (-r)•e)) = (-1)^n * p (x + (-r)•e).
  -- The factor (-1)^n is nonzero, so it does not change whether a value is zero.
  change (characteristicPolynomial p e x).eval r = 0 ↔
    (polynomialOnLine p e x).eval (-r) = 0
  rw [eval_characteristicPolynomial hp, eval_polynomialOnLine hp]
  have hvec : r • e - x = (-1 : ℝ) • (x + (-r) • e) := by
    simp [smul_add, smul_smul, sub_eq_add_neg, add_comm]
  rw [hvec, hp.map_smul]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)))

/-- If [a function is a homogeneous polynomial](hyp:hp),
then [membership in its closed hyperbolicity cone is equivalent to every root
of its line polynomial at that vector being nonpositive](goal). -/
theorem mem_hyperbolicityCone_iff_roots_nonpos {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) :
    x ∈ hyperbolicityCone p e ↔
      ∀ r : ℝ, (polynomialOnLine p e x).IsRoot r → r ≤ 0 := by
  constructor
  · intro hx r hr
    have h := hx (-r) ((isRoot_characteristicPolynomial_iff hp e x (-r)).2
      (by simpa using hr))
    exact neg_nonneg.mp h
  · intro hx r hr
    have h := hx (-r) ((isRoot_characteristicPolynomial_iff hp e x r).1 hr)
    exact neg_nonpos.mp h

/-- If [a function is a homogeneous polynomial of degree n](hyp:hp)
and [is positive at the direction](hyp:he), then
[every line polynomial in that direction has degree n and leading coefficient
equal to the function's value at that direction](goal). -/
theorem degree_leadingCoeff_polynomialOnLine {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) (he : 0 < p e) :
    (polynomialOnLine p e x).natDegree = n ∧
      (polynomialOnLine p e x).leadingCoeff = p e := by
  -- Combine the degree bound with the nonzero coefficient at n.
  have hd := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_polynomialOnLine_le hp e x)
    (show (polynomialOnLine p e x).coeff n ≠ 0 by
      rw [coeff_polynomialOnLine_degree hp e x]
      exact he.ne')
  exact ⟨hd, by
    rw [Polynomial.leadingCoeff, hd, coeff_polynomialOnLine_degree hp e x]⟩

/-- If [a function is a homogeneous polynomial of degree n](hyp:hp)
and [is hyperbolic in the chosen direction](hyp:he), then
[every vector has exactly n eigenvalues counted with multiplicity](goal). -/
theorem card_eigenvalues {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) (he : IsHyperbolic p e) :
    (eigenvalues p e x).card = n := by
  rw [eigenvalues, characteristicPolynomial,
    (he.2 (-x)).natDegree_eq_card_roots.symm,
    (degree_leadingCoeff_polynomialOnLine hp e (-x) he.1).1]

/-- If [a function is a homogeneous polynomial](hyp:hp)
and [is hyperbolic in the chosen direction](hyp:he), then
[its line polynomial is its value at the direction times the product of
the variable plus each eigenvalue](goal). -/
theorem polynomialOnLine_eq_prod_eigenvalues {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) (he : IsHyperbolic p e) :
    polynomialOnLine p e x = Polynomial.C (p e) *
      ((eigenvalues p e x).map (fun r => Polynomial.X + Polynomial.C r)).prod := by
  -- Factor the characteristic polynomial and reflect its variable: homogeneity
  -- gives the reflection identity with sign (-1)^n, and roots_C_mul together with
  -- roots_comp_neg_X identify the two root multisets with multiplicities.
  have hreflect : polynomialOnLine p e x = Polynomial.C ((-1 : ℝ) ^ n) *
      (characteristicPolynomial p e x).comp (-Polynomial.X) := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
      Polynomial.eval_neg, Polynomial.eval_X, eval_characteristicPolynomial hp,
      eval_polynomialOnLine hp]
    have hvec : x + t • e = (-1 : ℝ) • ((-t) • e - x) := by
      simp [smul_smul, sub_eq_add_neg, add_comm]
    rw [hvec, hp.map_smul]
  have hroots : (polynomialOnLine p e x).roots =
      (eigenvalues p e x).map (fun r => -r) := by
    rw [hreflect, Polynomial.roots_C_mul _ (pow_ne_zero n (by norm_num)),
      Polynomial.roots_comp_neg_X]
    rfl
  rw [(he.2 x).eq_prod_roots,
    (degree_leadingCoeff_polynomialOnLine hp e x he.1).2, hroots,
    Multiset.map_map]
  simp only [Function.comp_def, Polynomial.C_neg, sub_neg_eq_add]

/-- If [a function is a homogeneous polynomial of degree n](hyp:hp),
[is hyperbolic in the chosen direction](hyp:he), and
[the derivative order is at most n](hyp:hi), then
[its i-th directional derivative is i factorial times its value at the direction
times the elementary symmetric function of degree n minus i of the eigenvalues](goal).

This is Proposition 18 of Renegar's 2004 preprint. -/
theorem iteratedDirectionalDerivative_eq_esymm_eigenvalues {p : E → ℝ} {n : ℕ}
    (hp : IsHomogeneousPolynomial p n) (e x : E) (he : IsHyperbolic p e)
    (i : ℕ) (hi : i ≤ n) :
    iteratedDirectionalDerivative p e i x =
      (Nat.factorial i : ℝ) * p e * (eigenvalues p e x).esymm (n - i) := by
  -- Extract coefficient i in polynomialOnLine_eq_prod_eigenvalues and apply
  -- Multiset.prod_X_add_C_coeff, then the directional derivative coefficient formula.
  rw [iteratedDirectionalDerivative_eq_factorial_mul_coeff hp e x i,
    polynomialOnLine_eq_prod_eigenvalues hp e x he, Polynomial.coeff_C_mul,
    Multiset.prod_X_add_C_coeff (eigenvalues p e x)
      (by rw [card_eigenvalues hp e x he]; exact hi), card_eigenvalues hp e x he,
    mul_assoc]

/-- Let [a real-valued function on a finite-dimensional real vector space be a
homogeneous polynomial of degree n](hyp:hp), and suppose
[it is hyperbolic in the chosen direction](hyp:he). Then
[a vector belongs to its closed hyperbolicity cone, that is, all its eigenvalues are
nonnegative, exactly when its Renegar derivatives of orders 0, 1, …, n − 1 in that
direction are all nonnegative at that vector](goal).

This is Renegar's description of the closed hyperbolicity cone (Theorem 20 of the
2004 preprint, combined with Proposition 18). For the determinant on symmetric
matrices with a positive definite direction it describes the positive semidefinite
cone by finitely many polynomial inequalities. The characterization also holds in
degree zero: a positive constant has no eigenvalues, its closed cone is the whole
space, and no derivative signs are required. -/
theorem mem_hyperbolicityCone_iff_forall_iteratedDerivative_nonneg
    {p : E → ℝ} {n : ℕ} (hp : IsHomogeneousPolynomial p n)
    (e : E) (he : IsHyperbolic p e) (x : E) :
    x ∈ hyperbolicityCone p e ↔
      ∀ i : ℕ, i < n → 0 ≤ iteratedDirectionalDerivative p e i x := by
  -- Rewrite cone membership by mem_hyperbolicityCone_iff_roots_nonpos and apply
  -- roots_nonpos_iff_coeff_nonneg. Orders below n are equivalent to coefficient
  -- signs because i! > 0; coefficient n equals p(e) > 0 and higher ones vanish.
  rw [mem_hyperbolicityCone_iff_roots_nonpos hp e x,
    roots_nonpos_iff_coeff_nonneg (polynomialOnLine p e x) (he.2 x)
      (by rw [(degree_leadingCoeff_polynomialOnLine hp e x he.1).2]; exact he.1)]
  constructor
  · intro h i _
    rw [iteratedDirectionalDerivative_eq_factorial_mul_coeff hp e x i]
    exact mul_nonneg (Nat.cast_nonneg _) (h i)
  · intro h i
    rcases lt_trichotomy i n with hi | rfl | hi
    · have hd := h i hi
      rw [iteratedDirectionalDerivative_eq_factorial_mul_coeff hp e x i] at hd
      exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast Nat.factorial_pos i)).mp hd
    · rw [coeff_polynomialOnLine_degree hp e x]
      exact he.1.le
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        ((natDegree_polynomialOnLine_le hp e x).trans_lt hi)]

end Toolkit.Foundations.Algebra
