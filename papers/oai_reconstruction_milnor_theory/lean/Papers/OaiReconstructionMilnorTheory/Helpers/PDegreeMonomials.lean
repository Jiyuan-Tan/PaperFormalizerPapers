module

public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Fin

/-! # Polynomial exponent classes for the power-degree calculation

Grouping exponents modulo `p` gives a unique expansion in the monomials whose
individual exponents are less than `p`, with coefficients in the expanded
polynomial ring. These are the polynomial steps of the rational-function basis
calculation in the p-degree lemma.
-/

@[expose] public section

namespace Papers.OaiReconstructionMilnorTheory

open MvPolynomial

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

-- @node: powerResidueExponent
/-- For [a finite index set σ](hyp:σ) and [a tuple r of residues between zero and
p minus one](hyp:r), [the associated exponent vector](goal) assigns to each index
the nonnegative integer represented by its residue. -/
noncomputable def powerResidueExponent {p : ℕ} (r : σ → Fin p) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (r i).val)

-- @node: powerResidueExponent_apply
/-- [At each index i, the exponent vector associated with a residue tuple r has
value equal to the integer represented by the residue at i](goal). -/
lemma powerResidueExponent_apply {p : ℕ} (r : σ → Fin p) (i : σ) :
    powerResidueExponent r i = (r i).val := by
  simp [powerResidueExponent]

-- @node: powerResidueExponent_unique
/-- If [p is positive](hyp:hp) and [multiplying q and q′ by p and adding the
exponent vectors of r and r′ gives the same vector](hyp:h), then [q equals q′
and r equals r′](goal). -/
lemma powerResidueExponent_unique {p : ℕ} (hp : 0 < p)
    (q q' : σ →₀ ℕ) (r r' : σ → Fin p)
    (h : p • q + powerResidueExponent r = p • q' + powerResidueExponent r') :
    q = q' ∧ r = r' := by
  have hr : r = r' := by
    funext i
    apply Fin.ext
    have hi := congrArg (fun d : σ →₀ ℕ => d i % p) h
    simpa [powerResidueExponent_apply, Nat.add_mod, Nat.mod_eq_of_lt (r i).isLt,
      Nat.mod_eq_of_lt (r' i).isLt] using hi
  refine ⟨?_, hr⟩
  subst r'
  have hq : p • q = p • q' := add_right_cancel h
  ext i
  have hi := congrArg (fun d : σ →₀ ℕ => d i) hq
  simp only [Finsupp.smul_apply, smul_eq_mul] at hi
  exact Nat.eq_of_mul_eq_mul_left hp hi

-- @node: powerResidue_coeff_expand_mul
/-- If [p is positive](hyp:hp), then [the coefficient at exponent p times q plus
the residue vector r′, in the product of f with all exponents multiplied by p
and the monomial with residue vector r and coefficient one, is the coefficient
of f at q when r equals r′, and zero otherwise](goal). -/
lemma powerResidue_coeff_expand_mul {p : ℕ} (hp : 0 < p)
    (f : MvPolynomial σ R) (q : σ →₀ ℕ) (r r' : σ → Fin p) :
    coeff (p • q + powerResidueExponent r')
      (expand p f * monomial (powerResidueExponent r) 1) =
      if r = r' then coeff q f else 0 := by
  classical
  by_cases hr : r = r'
  · subst r'
    simp [coeff_mul_monomial, coeff_expand_smul p hp.ne']
  · rw [if_neg hr]
    conv_lhs => rw [f.as_sum]
    simp only [map_sum, expand_monomial, Finset.sum_mul, monomial_mul, mul_one,
      coeff_sum]
    apply Finset.sum_eq_zero
    intro d hd
    rw [coeff_monomial, if_neg]
    intro he
    exact hr (powerResidueExponent_unique hp d q r r' he).2

-- @node: powerResidue_monomial_decomposition
/-- If [p is positive](hyp:hp), then [every monomial with exponent vector d and
coefficient a can be written as a monomial with coefficient a and all exponents
multiplied by p, times a monomial with coefficient one and exponents between
zero and p minus one](goal). -/
lemma powerResidue_monomial_decomposition {p : ℕ} (hp : 0 < p)
    (d : σ →₀ ℕ) (a : R) :
    ∃ (r : σ → Fin p) (q : σ →₀ ℕ),
      monomial d a = expand p (monomial q a) * monomial (powerResidueExponent r) 1 := by
  let r : σ → Fin p := fun i => ⟨d i % p, Nat.mod_lt _ hp⟩
  let q : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => d i / p)
  refine ⟨r, q, ?_⟩
  rw [expand_monomial, monomial_mul, mul_one]
  have hd : d = p • q + powerResidueExponent r := by
    ext i
    simpa [q, r, powerResidueExponent_apply, Nat.add_comm] using
      (Nat.mod_add_div (d i) p).symm
  rw [hd]

variable [DecidableEq σ]

-- @node: powerResidue_polynomial_decomposition
/-- If [p is positive](hyp:hp), then [every polynomial f is a sum indexed by
residue tuples r, each term being a polynomial with all exponents multiplied
by p times the monomial with residue vector r and coefficient one](goal). -/
lemma powerResidue_polynomial_decomposition {p : ℕ} (hp : 0 < p)
    (f : MvPolynomial σ R) :
    ∃ g : (σ → Fin p) → MvPolynomial σ R,
      f = ∑ r, expand p (g r) * monomial (powerResidueExponent r) 1 := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    obtain ⟨r, q, h⟩ := powerResidue_monomial_decomposition hp d a
    refine ⟨fun r' => if r' = r then monomial q a else 0, ?_⟩
    simpa only [apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] using h
  | add f₁ f₂ h₁ h₂ =>
    obtain ⟨g₁, hg₁⟩ := h₁
    obtain ⟨g₂, hg₂⟩ := h₂
    refine ⟨fun r => g₁ r + g₂ r, ?_⟩
    simp only [map_add, add_mul, Finset.sum_add_distrib, ← hg₁, ← hg₂]

-- @node: powerResidue_polynomial_decomposition_unique
/-- For [positive p](hyp:hp), consider a polynomial family g and [a polynomial
family h indexed by residue tuples](hyp:h). If [their sums, formed by multiplying
all exponents in each polynomial by p and then multiplying by the corresponding
residue monomial, are equal](hyp:heq), then [the two polynomial families are equal](goal). -/
lemma powerResidue_polynomial_decomposition_unique {p : ℕ} (hp : 0 < p)
    (g h : (σ → Fin p) → MvPolynomial σ R)
    (heq : (∑ r, expand p (g r) * monomial (powerResidueExponent r) 1) =
      ∑ r, expand p (h r) * monomial (powerResidueExponent r) 1) : g = h := by
  classical
  funext r
  ext q
  have hc := congrArg (coeff (p • q + powerResidueExponent r)) heq
  simpa only [coeff_sum, powerResidue_coeff_expand_mul hp, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using hc

-- @node: powerResidue_card
/-- [The number of tuples assigning a residue between zero and p minus one to
each index in σ is p raised to the number of indices in σ](goal). -/
lemma powerResidue_card (p : ℕ) : Fintype.card (σ → Fin p) = p ^ Fintype.card σ := by
  simp

end Papers.OaiReconstructionMilnorTheory
