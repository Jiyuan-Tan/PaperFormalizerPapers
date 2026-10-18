module
public import Papers.TbsNeuralCausalPi.Helpers.PolynomialUnivariateComponents
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Separation.Basic
/-! # Polynomial arrangements restricted to polynomial curves

Substitution along a polynomial curve multiplies degree by its coordinate
degree. The real root arrangement therefore bounds the strict signs and the
connected components in the curve parameter. In particular affine lines
preserve degree. These slice bounds do not assert the multivariate component
estimate required for the uniform simulation sampling theorem.
-/
@[expose] public section
namespace Papers.TbsNeuralCausalPi
noncomputable section

-- @node: polynomialCurveRestriction
/-- For [a curve with polynomial coordinates](hyp:curve) and [a multivariate real
polynomial](hyp:p), the [restriction to the curve](goal) is the univariate
polynomial obtained by substituting the coordinate polynomials. -/
def polynomialCurveRestriction {V : Type*} (curve : V → Polynomial ℝ)
    (p : MvPolynomial V ℝ) : Polynomial ℝ := MvPolynomial.aeval curve p

-- @node: polynomialCurveRestriction_eval
/-- [Evaluating a polynomial restricted to a polynomial curve at a real parameter
equals evaluating the original polynomial at the corresponding point on the curve](goal). -/
lemma polynomialCurveRestriction_eval {V : Type*} (curve : V → Polynomial ℝ)
    (p : MvPolynomial V ℝ) (t : ℝ) :
    (polynomialCurveRestriction curve p).eval t =
      MvPolynomial.eval (fun v => (curve v).eval t) p := by
  exact MvPolynomial.comp_aeval_apply curve (Polynomial.aeval t) p

-- @node: polynomialCurveRestriction_natDegree_le
/-- If [every coordinate polynomial of a curve has degree at most k](hyp:hk),
then [restricting a multivariate polynomial to that curve gives a polynomial of
degree at most its total degree times k](goal). -/
lemma polynomialCurveRestriction_natDegree_le {V : Type*} (curve : V → Polynomial ℝ)
    (p : MvPolynomial V ℝ) (k : ℕ) (hk : ∀ v, (curve v).natDegree ≤ k) :
    (polynomialCurveRestriction curve p).natDegree ≤ p.totalDegree * k := by
  exact MvPolynomial.aeval_natDegree_le p le_rfl curve hk

-- @node: polynomialCurve_nonzero_domain_eq
/-- [The parameters at which every polynomial is nonzero along a polynomial curve
are exactly those at which every restricted univariate polynomial is nonzero](goal). -/
lemma polynomialCurve_nonzero_domain_eq {I V : Type*} (curve : V → Polynomial ℝ)
    (p : I → MvPolynomial V ℝ) :
    {t | ∀ i, MvPolynomial.eval (fun v => (curve v).eval t) (p i) ≠ 0} =
      {t | ∀ i, (polynomialCurveRestriction curve (p i)).eval t ≠ 0} := by
  ext t
  simp only [polynomialCurveRestriction_eval]

-- @node: polynomialCurve_strict_signPattern_encard_le
/-- If [each polynomial in a finite family has total degree at most d](hyp:hd)
and [each coordinate of a polynomial curve has degree at most k](hyp:hk), then
[the number of strict sign patterns attained where all polynomials are nonzero
along the curve is at most the family size times d times k, plus one](goal). -/
lemma polynomialCurve_strict_signPattern_encard_le {I V : Type*} [Fintype I]
    (curve : V → Polynomial ℝ) (p : I → MvPolynomial V ℝ) (d k : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) (hk : ∀ v, (curve v).natDegree ≤ k) :
    ((fun t => strictPolynomialSignPattern p (fun v => (curve v).eval t)) ''
      {t | ∀ i, MvPolynomial.eval (fun v => (curve v).eval t) (p i) ≠ 0}).encard ≤
        (Fintype.card I * (d * k) + 1 : ℕ) := by
  have he : (fun t => strictPolynomialSignPattern p (fun v => (curve v).eval t)) =
      univariateNonzeroSignPattern (fun i => polynomialCurveRestriction curve (p i)) := by
    funext t i
    simp only [strictPolynomialSignPattern, univariateNonzeroSignPattern,
      polynomialCurveRestriction_eval]
  rw [he, polynomialCurve_nonzero_domain_eq]
  exact univariate_nonzero_signPattern_encard_le_degree _ (d * k) (fun i =>
    (polynomialCurveRestriction_natDegree_le curve (p i) k hk).trans
      (Nat.mul_le_mul_right k (hd i)))

-- @node: polynomialCurve_nonzero_components_encard_le
/-- If [each polynomial in a finite family has total degree at most d](hyp:hd)
and [each coordinate of a polynomial curve has degree at most k](hyp:hk), then
[the set of parameters where all polynomials are nonzero has at most the family
size times d times k, plus one, connected components](goal). -/
lemma polynomialCurve_nonzero_components_encard_le {I V : Type*} [Fintype I]
    (curve : V → Polynomial ℝ) (p : I → MvPolynomial V ℝ) (d k : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) (hk : ∀ v, (curve v).natDegree ≤ k) :
    (realSetComponents
      {t | ∀ i, MvPolynomial.eval (fun v => (curve v).eval t) (p i) ≠ 0}).encard ≤
        (Fintype.card I * (d * k) + 1 : ℕ) := by
  rw [polynomialCurve_nonzero_domain_eq]
  exact univariate_nonzero_components_encard_le_degree _ (d * k) (fun i =>
    (polynomialCurveRestriction_natDegree_le curve (p i) k hk).trans
      (Nat.mul_le_mul_right k (hd i)))

-- @node: affineLinePolynomial
/-- For [a base point](hyp:a) and [a direction vector](hyp:direction), the
[polynomial coordinates of the affine line](goal) give each base coordinate
plus the corresponding direction coordinate times the real parameter. -/
def affineLinePolynomial {V : Type*} (a direction : V → ℝ) : V → Polynomial ℝ :=
  fun v => Polynomial.C (a v) + Polynomial.C (direction v) * Polynomial.X

-- @node: affineLinePolynomial_eval
/-- [Evaluating a coordinate polynomial of an affine line at a real parameter
gives the base coordinate plus the direction coordinate times that parameter](goal). -/
lemma affineLinePolynomial_eval {V : Type*} (a direction : V → ℝ) (v : V) (t : ℝ) :
    (affineLinePolynomial a direction v).eval t = a v + direction v * t := by
  simp [affineLinePolynomial]

-- @node: affineLinePolynomial_natDegree_le
/-- [Each coordinate polynomial of an affine line has degree at most one](goal). -/
lemma affineLinePolynomial_natDegree_le {V : Type*} (a direction : V → ℝ) (v : V) :
    (affineLinePolynomial a direction v).natDegree ≤ 1 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · exact (Polynomial.natDegree_mul_le).trans (by simp)

-- @node: affineLine_strict_signPattern_encard_le
/-- If [each polynomial in a finite family has total degree at most d](hyp:hd),
then [along any affine line the number of strict sign patterns attained where
all polynomials are nonzero is at most the family size times d, plus one](goal). -/
lemma affineLine_strict_signPattern_encard_le {I V : Type*} [Fintype I]
    (a direction : V → ℝ) (p : I → MvPolynomial V ℝ) (d : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    ((fun t => strictPolynomialSignPattern p (fun v => a v + direction v * t)) ''
      {t | ∀ i, MvPolynomial.eval (fun v => a v + direction v * t) (p i) ≠ 0}).encard ≤
        (Fintype.card I * d + 1 : ℕ) := by
  simpa only [affineLinePolynomial_eval, Nat.mul_one] using
    polynomialCurve_strict_signPattern_encard_le (affineLinePolynomial a direction) p d 1 hd
      (affineLinePolynomial_natDegree_le a direction)

-- @node: affineLine_nonzero_components_encard_le
/-- If [each polynomial in a finite family has total degree at most d](hyp:hd),
then [the set of real parameters on any affine line where all polynomials are
nonzero has at most the family size times d, plus one, connected components](goal). -/
lemma affineLine_nonzero_components_encard_le {I V : Type*} [Fintype I]
    (a direction : V → ℝ) (p : I → MvPolynomial V ℝ) (d : ℕ)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    (realSetComponents
      {t | ∀ i, MvPolynomial.eval (fun v => a v + direction v * t) (p i) ≠ 0}).encard ≤
        (Fintype.card I * d + 1 : ℕ) := by
  simpa only [affineLinePolynomial_eval, Nat.mul_one] using
    polynomialCurve_nonzero_components_encard_le (affineLinePolynomial a direction) p d 1 hd
      (affineLinePolynomial_natDegree_le a direction)

-- @node: realPolynomial_exists_nonzero_eval
/-- If [a multivariate real polynomial is not the zero polynomial](hyp:hp), then
[it is nonzero at some real point](goal). -/
lemma realPolynomial_exists_nonzero_eval {V : Type*} (p : MvPolynomial V ℝ)
    (hp : p ≠ 0) : ∃ a : V → ℝ, MvPolynomial.eval a p ≠ 0 := by
  by_contra h
  apply hp
  apply MvPolynomial.funext
  intro a
  simpa using not_exists.mp h a

-- @node: polynomialNonzeroDomain_nonempty
/-- If [every polynomial in a finite family is not the zero polynomial](hyp:hp),
then [there is a real point where all polynomials in the family are nonzero](goal). -/
lemma polynomialNonzeroDomain_nonempty {I V : Type*} [Finite I]
    (p : I → MvPolynomial V ℝ) (hp : ∀ i, p i ≠ 0) :
    (polynomialNonzeroDomain p).Nonempty := by
  classical
  let := Fintype.ofFinite I
  have hprod : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  obtain ⟨a, ha⟩ := realPolynomial_exists_nonzero_eval (∏ i, p i) hprod
  refine ⟨a, ?_⟩
  rw [polynomialNonzeroDomain_eq_product_complement]
  exact ha

-- @node: affineLine_nonzero_domain_dense
/-- If [all polynomials in a finite family are nonzero at the point b](hyp:hb),
then [the real parameters where all remain nonzero along the line from any
point a toward b form a dense subset of the real line](goal). -/
lemma affineLine_nonzero_domain_dense {I V : Type*} [Finite I]
    (p : I → MvPolynomial V ℝ) (a b : V → ℝ)
    (hb : b ∈ polynomialNonzeroDomain p) :
    Dense {t : ℝ | ∀ i,
      MvPolynomial.eval (fun v => a v + (b v - a v) * t) (p i) ≠ 0} := by
  classical
  let := Fintype.ofFinite I
  let q : I → Polynomial ℝ := fun i =>
    polynomialCurveRestriction (affineLinePolynomial a (fun v => b v - a v)) (p i)
  have hq : ∀ i, q i ≠ 0 := by
    intro i hi
    have he : (q i).eval 1 = MvPolynomial.eval b (p i) := by
      simp [q, polynomialCurveRestriction_eval, affineLinePolynomial_eval]
    apply hb i
    rw [← he, hi]
    simp
  have hd : Dense ((polynomialArrangementRoots q : Set ℝ)ᶜ) := by
    convert (dense_univ.sdiff_finset (polynomialArrangementRoots q)) using 1
    ext t
    simp
  have he : {t : ℝ | ∀ i,
      MvPolynomial.eval (fun v => a v + (b v - a v) * t) (p i) ≠ 0} =
      (polynomialArrangementRoots q : Set ℝ)ᶜ := by
    rw [← univariate_nonzero_domain_eq_roots_complement q hq]
    ext t
    simp only [q, polynomialCurveRestriction_eval, affineLinePolynomial_eval]
  rwa [he]

-- @node: polynomialNonzeroDomain_dense
/-- If [every polynomial in a finite family is not the zero polynomial](hyp:hp),
then [the real points where all polynomials are nonzero form a dense set](goal). -/
lemma polynomialNonzeroDomain_dense {I V : Type*} [Finite I]
    (p : I → MvPolynomial V ℝ) (hp : ∀ i, p i ≠ 0) :
    Dense (polynomialNonzeroDomain p) := by
  obtain ⟨b, hb⟩ := polynomialNonzeroDomain_nonempty p hp
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨a, ha⟩ := hUne
  let line : ℝ → (V → ℝ) := fun t v => a v + (b v - a v) * t
  have hline : Continuous line := by fun_prop
  have hpre : (line ⁻¹' U).Nonempty := ⟨0, by simpa [line] using ha⟩
  obtain ⟨t, ht, hgood⟩ := (affineLine_nonzero_domain_dense p a b hb).inter_open_nonempty
    (line ⁻¹' U) (hU.preimage hline) hpre
  exact ⟨line t, ht, hgood⟩

end
end Papers.TbsNeuralCausalPi
