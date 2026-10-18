module
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialSignPerturbation
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Order.IntermediateValue
/-! # Polynomial signs and components of a hypersurface complement

Strict signs are constant on each connected component of the complement of
the polynomial zero sets. Their number is therefore bounded by the number of
components of the complement of the product zero set. The same reduction
applies to weak/strict comparison pairs after the existing one-variable shift.
No degree-dependent bound on real algebraic components is asserted here.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: polynomialNonzeroDomain
/-- For [a family of real polynomials](hyp:p), the [simultaneous nonzero
domain](goal) is the set of variable assignments at which every polynomial in
the family has a nonzero value. -/
def polynomialNonzeroDomain {I V : Type*} (p : I → MvPolynomial V ℝ) : Set (V → ℝ) :=
  {a | ∀ i, MvPolynomial.eval a (p i) ≠ 0}

-- @node: polynomialSignComponents
/-- For [a family of real polynomials](hyp:p), the [sign components](goal) are
the connected components of the set of assignments where every polynomial is
nonzero, represented as subsets of the assignment space.

No finiteness or regular-value assumption is required. -/
def polynomialSignComponents {I V : Type*} (p : I → MvPolynomial V ℝ) :
    Set (Set (V → ℝ)) :=
  (fun a => connectedComponentIn (polynomialNonzeroDomain p) a) ''
    polynomialNonzeroDomain p

-- @node: polynomialNonzeroDomain_isOpen
/-- For a finite family of real polynomials, [the set of assignments where
every polynomial has a nonzero value is open](goal). -/
lemma polynomialNonzeroDomain_isOpen {I V : Type*} [Finite I]
    (p : I → MvPolynomial V ℝ) : IsOpen (polynomialNonzeroDomain p) := by
  simp only [polynomialNonzeroDomain, Set.ofPred_forall]
  exact isOpen_iInter_of_finite (fun i =>
    isOpen_ne.preimage (MvPolynomial.continuous_eval (p i)))

-- @node: sign_eq_on_preconnected_nonzero
/-- If [a subset of a topological space is connected](hyp:hs), a real-valued
function is [continuous on that subset](hyp:hf) and [nonzero throughout it](hyp:hn),
and [a first point](hyp:hx) and [a second point](hyp:hy) belong to the subset,
then [the function is negative at the first point if and only if it is negative
at the second](goal). -/
lemma sign_eq_on_preconnected_nonzero {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsPreconnected s) (f : X → ℝ) (hf : ContinuousOn f s)
    (hn : ∀ x ∈ s, f x ≠ 0) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    f x < 0 ↔ f y < 0 := by
  constructor
  · intro hxn
    by_contra hyn
    have hyp : 0 < f y := lt_of_le_of_ne (le_of_not_gt hyn) (hn y hy).symm
    obtain ⟨z, hz, hzero⟩ := hs.intermediate_value hx hy hf
      (show (0 : ℝ) ∈ Set.Icc (f x) (f y) from ⟨hxn.le, hyp.le⟩)
    exact hn z hz hzero
  · intro hyn
    by_contra hxn
    have hxp : 0 < f x := lt_of_le_of_ne (le_of_not_gt hxn) (hn x hx).symm
    obtain ⟨z, hz, hzero⟩ := hs.intermediate_value hy hx hf
      (show (0 : ℝ) ∈ Set.Icc (f y) (f x) from ⟨hyn.le, hxp.le⟩)
    exact hn z hz hzero

-- @node: strictPolynomialSignPattern_eq_on_component
/-- If [every polynomial in a family is nonzero at a first assignment](hyp:hx)
and [a second assignment lies in the first assignment's connected component
within the simultaneous nonzero domain](hyp:hy), then [the strict sign patterns
at the two assignments agree](goal). -/
lemma strictPolynomialSignPattern_eq_on_component {I V : Type*}
    (p : I → MvPolynomial V ℝ) {x y : V → ℝ}
    (hx : x ∈ polynomialNonzeroDomain p)
    (hy : y ∈ connectedComponentIn (polynomialNonzeroDomain p) x) :
    strictPolynomialSignPattern p x = strictPolynomialSignPattern p y := by
  funext i
  apply Bool.decide_congr
  exact sign_eq_on_preconnected_nonzero isPreconnected_connectedComponentIn
    (fun a => MvPolynomial.eval a (p i)) (MvPolynomial.continuous_eval (p i)).continuousOn
    (fun a ha => (connectedComponentIn_subset (polynomialNonzeroDomain p) x ha) i)
    (mem_connectedComponentIn hx) hy

-- @node: strictPolynomialSignPattern_encard_le_components
/-- [The number of strict sign patterns attained where every polynomial in a
family is nonzero is at most the number of connected components of that
simultaneous nonzero domain](goal).

Distinct sign patterns cannot have witnesses in the same component. -/
lemma strictPolynomialSignPattern_encard_le_components {I V : Type*}
    (p : I → MvPolynomial V ℝ) :
    (strictPolynomialSignPattern p '' polynomialNonzeroDomain p).encard ≤
      (polynomialSignComponents p).encard := by
  classical
  let patterns := strictPolynomialSignPattern p '' polynomialNonzeroDomain p
  have hw (v : patterns) : ∃ x, x ∈ polynomialNonzeroDomain p ∧
      strictPolynomialSignPattern p x = v.val := v.property
  choose x hx hpattern using hw
  let component : patterns → Set (V → ℝ) :=
    fun v => connectedComponentIn (polynomialNonzeroDomain p) (x v)
  have hinj : Function.Injective component := by
    intro v w h
    have hwmem : x w ∈ connectedComponentIn (polynomialNonzeroDomain p) (x v) := by
      rw [show connectedComponentIn (polynomialNonzeroDomain p) (x v) =
        connectedComponentIn (polynomialNonzeroDomain p) (x w) from h]
      exact mem_connectedComponentIn (hx w)
    apply Subtype.ext
    exact (hpattern v).symm.trans
      ((strictPolynomialSignPattern_eq_on_component p (hx v) hwmem).trans (hpattern w))
  calc
    patterns.encard ≤ (Set.range component).encard := hinj.encard_range
    _ ≤ (polynomialSignComponents p).encard := Set.encard_mono (by
      rintro _ ⟨v, rfl⟩
      exact ⟨x v, hx v, rfl⟩)

-- @node: polynomialNonzeroDomain_eq_product_complement
/-- For a finite family of real polynomials, [the set of assignments where every
member is nonzero equals the set where their product is nonzero](goal).

This includes empty families and zero polynomials. -/
lemma polynomialNonzeroDomain_eq_product_complement {I V : Type*} [Fintype I]
    (p : I → MvPolynomial V ℝ) :
    polynomialNonzeroDomain p = {a | MvPolynomial.eval a (∏ i, p i) ≠ 0} := by
  classical
  ext a
  simp [polynomialNonzeroDomain, map_prod, Finset.prod_ne_zero_iff]

-- @node: polynomialArrangementProduct_degree
/-- If [every polynomial in a finite family has total degree at most a common
bound](hyp:hd), then [their product has total degree at most the family size
times that bound](goal). -/
lemma polynomialArrangementProduct_degree {I V : Type*} [Fintype I]
    (p : I → MvPolynomial V ℝ) (d : ℕ) (hd : ∀ i, (p i).totalDegree ≤ d) :
    (∏ i, p i).totalDegree ≤ Fintype.card I * d := by
  classical
  exact (MvPolynomial.totalDegree_finsetProd _ _).trans
    ((Finset.sum_le_sum (fun i _ => hd i)).trans_eq (by simp))

-- @node: polynomialComparisonPattern_encard_le_components
/-- For a finite family of real polynomials, [the number of patterns recording
both nonpositivity and strict negativity over all assignments is at most the
number of connected components where all polynomials in the doubled shifted
family are nonzero](goal).

The shifted family adds and subtracts one extra variable from each original
polynomial. -/
lemma polynomialComparisonPattern_encard_le_components {I V : Type*} [Finite I]
    (p : I → MvPolynomial V ℝ) :
    (Set.range (polynomialComparisonPattern p)).encard ≤
      (polynomialSignComponents
        (fun ib : I × Bool => signShiftPolynomial (p ib.1) ib.2)).encard := by
  let := Fintype.ofFinite I
  exact (polynomialComparisonPattern_encard_le_nonzero p).trans
    (strictPolynomialSignPattern_encard_le_components _)

-- @node: shiftedPolynomialArrangementProduct_degree
/-- If [every polynomial in a finite family has total degree at most a common
bound](hyp:hd), then [the product of the two shifts of each member, formed by
adding and subtracting one extra variable, has total degree at most twice the
family size times the larger of that bound and one](goal). -/
lemma shiftedPolynomialArrangementProduct_degree {I V : Type*} [Fintype I]
    (p : I → MvPolynomial V ℝ) (d : ℕ) (hd : ∀ i, (p i).totalDegree ≤ d) :
    (∏ ib : I × Bool, signShiftPolynomial (p ib.1) ib.2).totalDegree ≤
      2 * Fintype.card I * max d 1 := by
  classical
  have h := polynomialArrangementProduct_degree
    (fun ib : I × Bool => signShiftPolynomial (p ib.1) ib.2) (max d 1)
    (fun ib => (signShiftPolynomial_degree _ _).trans (max_le_max (hd ib.1) le_rfl))
  simpa only [Fintype.card_prod, Fintype.card_bool, mul_comm (Fintype.card I) 2] using h

-- @node: polynomialZeroIntersection
/-- For [a finite set of indices](hyp:s) and [a family of real polynomials](hyp:p),
the [zero-intersection polynomial](goal) is the sum of the squares of the
polynomials at those indices.

Its zero set is their common zero set, including when the index set is empty. -/
def polynomialZeroIntersection {I V : Type*} (s : Finset I)
    (p : I → MvPolynomial V ℝ) : MvPolynomial V ℝ :=
  ∑ i ∈ s, p i ^ 2

-- @node: polynomialZeroIntersection_eval
/-- [Evaluating the zero-intersection polynomial at any assignment gives the
sum of the squared values of the polynomials at the selected indices](goal). -/
lemma polynomialZeroIntersection_eval {I V : Type*} (s : Finset I)
    (p : I → MvPolynomial V ℝ) (a : V → ℝ) :
    MvPolynomial.eval a (polynomialZeroIntersection s p) =
      ∑ i ∈ s, MvPolynomial.eval a (p i) ^ 2 := by
  simp [polynomialZeroIntersection, map_sum, map_pow]

-- @node: polynomialZeroIntersection_nonneg
/-- [The zero-intersection polynomial has a nonnegative value at every real
assignment](goal). -/
lemma polynomialZeroIntersection_nonneg {I V : Type*} (s : Finset I)
    (p : I → MvPolynomial V ℝ) (a : V → ℝ) :
    0 ≤ MvPolynomial.eval a (polynomialZeroIntersection s p) := by
  rw [polynomialZeroIntersection_eval]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

-- @node: polynomialZeroIntersection_eq_zero_iff
/-- [The zero-intersection polynomial vanishes at an assignment if and only if
every polynomial at a selected index vanishes at that assignment](goal). -/
lemma polynomialZeroIntersection_eq_zero_iff {I V : Type*} (s : Finset I)
    (p : I → MvPolynomial V ℝ) (a : V → ℝ) :
    MvPolynomial.eval a (polynomialZeroIntersection s p) = 0 ↔
      ∀ i ∈ s, MvPolynomial.eval a (p i) = 0 := by
  rw [polynomialZeroIntersection_eval,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  simp only [sq_eq_zero_iff]

-- @node: polynomialZeroIntersection_degree
/-- If [every polynomial at a selected index has total degree at most a common
bound](hyp:hd), then [the zero-intersection polynomial has total degree at most
twice that bound](goal). -/
lemma polynomialZeroIntersection_degree {I V : Type*} (s : Finset I)
    (p : I → MvPolynomial V ℝ) (d : ℕ)
    (hd : ∀ i ∈ s, (p i).totalDegree ≤ d) :
    (polynomialZeroIntersection s p).totalDegree ≤ 2 * d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (MvPolynomial.totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 (hd i hi))

end
end Papers.TbsNeuralCausalPi
