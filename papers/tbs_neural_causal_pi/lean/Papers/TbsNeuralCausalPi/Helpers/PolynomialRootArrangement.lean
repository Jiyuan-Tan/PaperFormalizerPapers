module
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialSignPerturbation
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
/-! # The one-dimensional polynomial root arrangement

The roots cut the real line into at most the sum of the degrees plus one
open cells. Simultaneous nonzero signs are constant on each cell. This is
the one-dimensional base case only; the multivariate arrangement estimate
needed for simulation sampling remains a separate obligation.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section
open Polynomial

-- @node: polynomialArrangementRoots
/-- For [a finite family of real univariate polynomials](hyp:p), the [arrangement
root set](goal) consists of all distinct real roots of the family. -/
def polynomialArrangementRoots {I : Type*} [Fintype I] (p : I → Polynomial ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.biUnion (fun i => (p i).roots.toFinset)

-- @node: polynomialArrangementRoots_card_le
/-- [The number of distinct real roots in a finite polynomial family is at most
the sum of its degrees](goal). -/
lemma polynomialArrangementRoots_card_le {I : Type*} [Fintype I]
    (p : I → Polynomial ℝ) :
    (polynomialArrangementRoots p).card ≤ ∑ i, (p i).natDegree := by
  classical
  exact (Finset.card_biUnion_le).trans (Finset.sum_le_sum (fun i _ =>
    (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' (p i))))

-- @node: polynomialArrangementRoots_mem
/-- If [a member of a finite polynomial family is not the zero polynomial](hyp:hpi)
and [it vanishes at a real point](hyp:hx), then [that point belongs to the
family's arrangement root set](goal). -/
lemma polynomialArrangementRoots_mem {I : Type*} [Fintype I]
    (p : I → Polynomial ℝ) (i : I) (hpi : p i ≠ 0) {x : ℝ}
    (hx : (p i).eval x = 0) : x ∈ polynomialArrangementRoots p := by
  classical
  simp only [polynomialArrangementRoots, Finset.mem_biUnion, Finset.mem_univ,
    Multiset.mem_toFinset, true_and]
  exact ⟨i, (Polynomial.mem_roots hpi).mpr hx⟩

-- @node: finite_root_cut_eq_of_card_eq
/-- If [a finite set of real numbers has equally many elements at or below each
of two thresholds](hyp:h), then [the subsets at or below those thresholds are
equal](goal). -/
lemma finite_root_cut_eq_of_card_eq (s : Finset ℝ) (x y : ℝ)
    (h : (s.filter (· ≤ x)).card = (s.filter (· ≤ y)).card) :
    s.filter (· ≤ x) = s.filter (· ≤ y) := by
  classical
  rcases le_total x y with hxy | hyx
  · apply Finset.eq_of_subset_of_card_le _ h.ge
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
      (Finset.mem_filter.mp hz).2.trans hxy⟩
  · symm
    apply Finset.eq_of_subset_of_card_le _ h.le
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
      (Finset.mem_filter.mp hz).2.trans hyx⟩

-- @node: polynomial_sign_eq_of_no_root_between
/-- If [one real point is at or below another](hyp:hxy), a real polynomial is
[nonzero at the first point](hyp:hx) and [nonzero at the second point](hyp:hy),
and [it has no zeros strictly between them](hyp:hn), then [its value at the
first point is negative if and only if its value at the second is negative](goal). -/
lemma polynomial_sign_eq_of_no_root_between (p : Polynomial ℝ) {x y : ℝ}
    (hxy : x ≤ y) (hx : p.eval x ≠ 0) (hy : p.eval y ≠ 0)
    (hn : ∀ z ∈ Set.Ioo x y, p.eval z ≠ 0) :
    p.eval x < 0 ↔ p.eval y < 0 := by
  constructor
  · intro hxneg
    by_contra hyneg
    have hypos : 0 < p.eval y := lt_of_le_of_ne (le_of_not_gt hyneg) hy.symm
    obtain ⟨z, hz, he⟩ := intermediate_value_Icc hxy p.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (p.eval x) (p.eval y) from ⟨hxneg.le, hypos.le⟩)
    have hzx : x < z := lt_of_le_of_ne hz.1 (by intro h; subst z; exact hx he)
    have hzy : z < y := lt_of_le_of_ne hz.2 (by intro h; subst z; exact hy he)
    exact hn z ⟨hzx, hzy⟩ he
  · intro hyneg
    by_contra hxneg
    have hxpos : 0 < p.eval x := lt_of_le_of_ne (le_of_not_gt hxneg) hx.symm
    obtain ⟨z, hz, he⟩ := intermediate_value_Icc' hxy p.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (p.eval y) (p.eval x) from ⟨hyneg.le, hxpos.le⟩)
    have hzx : x < z := lt_of_le_of_ne hz.1 (by intro h; subst z; exact hx he)
    have hzy : z < y := lt_of_le_of_ne hz.2 (by intro h; subst z; exact hy he)
    exact hn z ⟨hzx, hzy⟩ he

-- @node: univariateNonzeroSignPattern
/-- For [a family of real univariate polynomials](hyp:p) and [a real evaluation
point](hyp:x), the [sign pattern](goal) records whether each polynomial's value
at that point is strictly negative. -/
def univariateNonzeroSignPattern {I : Type*} (p : I → Polynomial ℝ) (x : ℝ) : I → Bool :=
  fun i => decide ((p i).eval x < 0)

-- @node: univariate_signPattern_eq_of_cut_eq
/-- If [every polynomial in a finite family is nonzero at a first point](hyp:hx)
and [at a second point](hyp:hy), and [the numbers of distinct arrangement roots
at or below the two points agree](hyp:hcut), then [all strict-negativity
indicators agree at the two points](goal). -/
lemma univariate_signPattern_eq_of_cut_eq {I : Type*} [Fintype I]
    (p : I → Polynomial ℝ) {x y : ℝ}
    (hx : ∀ i, (p i).eval x ≠ 0) (hy : ∀ i, (p i).eval y ≠ 0)
    (hcut : ((polynomialArrangementRoots p).filter (· ≤ x)).card =
      ((polynomialArrangementRoots p).filter (· ≤ y)).card) :
    univariateNonzeroSignPattern p x = univariateNonzeroSignPattern p y := by
  classical
  have hc := finite_root_cut_eq_of_card_eq (polynomialArrangementRoots p) x y hcut
  have ordered (a b : ℝ) (hab : a ≤ b)
      (ha : ∀ i, (p i).eval a ≠ 0) (hb : ∀ i, (p i).eval b ≠ 0)
      (hc : (polynomialArrangementRoots p).filter (· ≤ a) =
        (polynomialArrangementRoots p).filter (· ≤ b)) :
      univariateNonzeroSignPattern p a = univariateNonzeroSignPattern p b := by
    funext i
    apply Bool.decide_congr
    apply polynomial_sign_eq_of_no_root_between (p i) hab (ha i) (hb i)
    intro z hz he
    have hpi : p i ≠ 0 := by intro h; simpa [h] using ha i
    have hm := polynomialArrangementRoots_mem p i hpi he
    have hzcut : z ∈ (polynomialArrangementRoots p).filter (· ≤ b) :=
      Finset.mem_filter.mpr ⟨hm, hz.2.le⟩
    rw [← hc] at hzcut
    exact (not_le_of_gt hz.1) (Finset.mem_filter.mp hzcut).2
  rcases le_total x y with hxy | hyx
  · exact ordered x y hxy hx hy hc
  · exact (ordered y x hyx hy hx hc.symm).symm

-- @node: univariate_nonzero_signPattern_encard_le
/-- [The number of distinct sign patterns attained by a finite family of real
univariate polynomials at points where every member is nonzero is at most the
sum of the degrees plus one](goal).

This includes empty families and polynomials of degree zero. -/
lemma univariate_nonzero_signPattern_encard_le {I : Type*} [Fintype I]
    (p : I → Polynomial ℝ) :
    (univariateNonzeroSignPattern p '' {x | ∀ i, (p i).eval x ≠ 0}).encard ≤
      (∑ i, (p i).natDegree : ℕ) + 1 := by
  classical
  let patterns := univariateNonzeroSignPattern p '' {x | ∀ i, (p i).eval x ≠ 0}
  have hw (v : patterns) : ∃ x : ℝ,
      (∀ i, (p i).eval x ≠ 0) ∧ univariateNonzeroSignPattern p x = v.val :=
    v.property
  choose x hx hpattern using hw
  let rank : patterns → ℕ := fun v =>
    ((polynomialArrangementRoots p).filter (· ≤ x v)).card
  have hinj : Function.Injective rank := by
    intro v w h
    apply Subtype.ext
    exact (hpattern v).symm.trans
      ((univariate_signPattern_eq_of_cut_eq p (hx v) (hx w) h).trans (hpattern w))
  have hbound : Set.range rank ⊆ {k : ℕ | k < (polynomialArrangementRoots p).card + 1} := by
    rintro _ ⟨v, rfl⟩
    exact Nat.lt_succ_of_le (Finset.card_filter_le _ _)
  calc
    patterns.encard ≤ (Set.range rank).encard := hinj.encard_range
    _ ≤ {k : ℕ | k < (polynomialArrangementRoots p).card + 1}.encard :=
      Set.encard_mono hbound
    _ = ((polynomialArrangementRoots p).card + 1 : ℕ) := Set.Nat.encard_range _
    _ ≤ (∑ i, (p i).natDegree : ℕ) + 1 := by
      exact_mod_cast Nat.add_le_add_right (polynomialArrangementRoots_card_le p) 1

-- @node: univariate_nonzero_signPattern_encard_le_degree
/-- If [every polynomial in a finite univariate family has degree at most a
common bound](hyp:hd), then [the number of sign patterns attained where all
members are nonzero is at most the family size times that bound plus one](goal). -/
lemma univariate_nonzero_signPattern_encard_le_degree {I : Type*} [Fintype I]
    (p : I → Polynomial ℝ) (d : ℕ) (hd : ∀ i, (p i).natDegree ≤ d) :
    (univariateNonzeroSignPattern p '' {x | ∀ i, (p i).eval x ≠ 0}).encard ≤
      (Fintype.card I * d + 1 : ℕ) := by
  have hdeg : (∑ i, (p i).natDegree) ≤ Fintype.card I * d :=
    (Finset.sum_le_sum (fun i _ => hd i)).trans_eq (by simp)
  exact (univariate_nonzero_signPattern_encard_le p).trans (by
    exact_mod_cast Nat.add_le_add_right hdeg 1)

-- @node: unique_variable_polynomial_natDegree_le
/-- [Converting a polynomial with exactly one variable into a univariate
polynomial gives a degree no greater than its original total degree](goal). -/
lemma unique_variable_polynomial_natDegree_le {V : Type*} [Unique V]
    (p : MvPolynomial V ℝ) :
    (MvPolynomial.uniqueAlgEquiv ℝ V p).natDegree ≤ p.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  change p.totalDegree < (Finsupp.single (default : V) k).sum (fun _ n => n)
  simpa using hk

-- @node: unique_variable_polynomial_eval
/-- [Evaluating the univariate form of a polynomial with exactly one variable
at that variable's assigned value gives the same result as evaluating the
original polynomial at the assignment](goal). -/
lemma unique_variable_polynomial_eval {V : Type*} [Unique V]
    (p : MvPolynomial V ℝ) (a : V → ℝ) :
    (MvPolynomial.uniqueAlgEquiv ℝ V p).eval (a default) = MvPolynomial.eval a p := by
  exact MvPolynomial.eval₂_uniqueAlgEquiv

-- @node: strictPolynomialSignPattern_encard_le_one_variable
/-- For a finite polynomial family with exactly one variable, if [every member
has total degree at most a common bound](hyp:hd), then [the number of strict
sign patterns attained where all members are nonzero is at most the family
size times that bound plus one](goal).

This includes degree zero and an empty family. -/
lemma strictPolynomialSignPattern_encard_le_one_variable {I V : Type*}
    [Fintype I] [Unique V] (p : I → MvPolynomial V ℝ) (d : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    (strictPolynomialSignPattern p '' {a | ∀ i, MvPolynomial.eval a (p i) ≠ 0}).encard ≤
      (Fintype.card I * d + 1 : ℕ) := by
  let q : I → Polynomial ℝ := fun i => MvPolynomial.uniqueAlgEquiv ℝ V (p i)
  have hs : strictPolynomialSignPattern p '' {a | ∀ i, MvPolynomial.eval a (p i) ≠ 0} ⊆
      univariateNonzeroSignPattern q '' {x | ∀ i, (q i).eval x ≠ 0} := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a default, ?_, ?_⟩
    · intro i
      simpa only [q, unique_variable_polynomial_eval] using ha i
    · funext i
      simp only [univariateNonzeroSignPattern, strictPolynomialSignPattern, q,
        unique_variable_polynomial_eval]
  exact (Set.encard_mono hs).trans
    (univariate_nonzero_signPattern_encard_le_degree q d (fun i =>
      (unique_variable_polynomial_natDegree_le (p i)).trans (hd i)))

-- @node: strictPolynomialSignPattern_encard_le_no_variables
/-- For a polynomial family with no variables, [at most one strict sign pattern
is attained over all assignments](goal). -/
lemma strictPolynomialSignPattern_encard_le_no_variables {I V : Type*} [IsEmpty V]
    (p : I → MvPolynomial V ℝ) :
    (Set.range (strictPolynomialSignPattern p)).encard ≤ 1 := by
  let a : V → ℝ := fun v => isEmptyElim v
  have hs : Set.range (strictPolynomialSignPattern p) ⊆ {strictPolynomialSignPattern p a} := by
    rintro _ ⟨b, rfl⟩
    have hba : b = a := by funext v; exact isEmptyElim v
    exact Set.mem_singleton_iff.mpr (congrArg (strictPolynomialSignPattern p) hba)
  exact (Set.encard_mono hs).trans (by simp)

-- @node: strictPolynomialSignPattern_encard_le_degree_zero
/-- If [every polynomial in a family has total degree zero](hyp:hd), then [at
most one strict sign pattern is attained over all assignments, including
assignments where some polynomials vanish](goal). -/
lemma strictPolynomialSignPattern_encard_le_degree_zero {I V : Type*}
    (p : I → MvPolynomial V ℝ) (hd : ∀ i, (p i).totalDegree = 0) :
    (Set.range (strictPolynomialSignPattern p)).encard ≤ 1 := by
  let v : I → Bool := fun i => decide ((p i).coeff 0 < 0)
  have hs : Set.range (strictPolynomialSignPattern p) ⊆ {v} := by
    rintro _ ⟨a, rfl⟩
    apply Set.mem_singleton_iff.mpr
    funext i
    dsimp only [strictPolynomialSignPattern, v]
    rw [(MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp (hd i), MvPolynomial.eval_C]
    simp
  exact (Set.encard_mono hs).trans (by simp)

end
end Papers.TbsNeuralCausalPi
