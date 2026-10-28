module

public import Papers.OaiExactSemidefiniteLift.Basic

/-!
# Polynomial degree bookkeeping for the determinant

Linear coordinates, cofactors, and the two quadratic factors in Φ give
homogeneous entries of degree five, hence a determinant of degree twenty.
-/

public section

namespace Papers.OaiExactSemidefiniteLift

open Matrix
open Toolkit.Foundations.Algebra

section PolynomialOperations

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

-- @node: homogeneous_linear_coordinate
/-- For [a real linear functional f on a finite-dimensional real vector space](hyp:f),
[f is a homogeneous polynomial of degree one](goal). -/
lemma homogeneous_linear_coordinate (f : E →ₗ[ℝ] ℝ) :
    IsHomogeneousPolynomial f 1 := by
  classical
  let b := Module.finBasis ℝ E
  refine ⟨∑ i, MvPolynomial.C (f (b i)) * MvPolynomial.X i, ?_, ?_⟩
  · exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ =>
      (MvPolynomial.isHomogeneous_X ℝ i).C_mul _)
  · intro x
    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using
      congrArg f (b.sum_repr x)

-- @node: homogeneous_function_mul
/-- If [f is a homogeneous polynomial of degree m](hyp:hf) and
[g is a homogeneous polynomial of degree n](hyp:hg), then
[their pointwise product is homogeneous of degree m + n](goal). -/
lemma homogeneous_function_mul {f g : E → ℝ} {m n : ℕ}
    (hf : IsHomogeneousPolynomial f m) (hg : IsHomogeneousPolynomial g n) :
    IsHomogeneousPolynomial (fun x => f x * g x) (m + n) := by
  obtain ⟨p, hp, hv⟩ := hf
  obtain ⟨q, hq, hw⟩ := hg
  exact ⟨p * q, hp.mul hq, fun x => by simp [hv, hw]⟩

-- @node: homogeneous_function_sub
/-- If [f is a homogeneous polynomial of degree n](hyp:hf) and
[g is a homogeneous polynomial of the same degree](hyp:hg), then
[their pointwise difference is homogeneous of degree n](goal). -/
lemma homogeneous_function_sub {f g : E → ℝ} {n : ℕ}
    (hf : IsHomogeneousPolynomial f n) (hg : IsHomogeneousPolynomial g n) :
    IsHomogeneousPolynomial (fun x => f x - g x) n := by
  obtain ⟨p, hp, hv⟩ := hf
  obtain ⟨q, hq, hw⟩ := hg
  exact ⟨p - q, hp.sub hq, fun x => by simp [hv, hw]⟩

-- @node: homogeneous_function_add
/-- If [f is a homogeneous polynomial of degree n](hyp:hf) and
[g is a homogeneous polynomial of the same degree](hyp:hg), then
[their pointwise sum is homogeneous of degree n](goal). -/
lemma homogeneous_function_add {f g : E → ℝ} {n : ℕ}
    (hf : IsHomogeneousPolynomial f n) (hg : IsHomogeneousPolynomial g n) :
    IsHomogeneousPolynomial (fun x => f x + g x) n := by
  obtain ⟨p, hp, hv⟩ := hf
  obtain ⟨q, hq, hw⟩ := hg
  exact ⟨p + q, hp.add hq, fun x => by simp [hv, hw]⟩

-- @node: homogeneous_function_const_mul
/-- If [f is a homogeneous polynomial of degree n](hyp:hf), then for
[any real constant c](hyp:c), [multiplying f by c preserves homogeneity of degree n](goal). -/
lemma homogeneous_function_const_mul {f : E → ℝ} {n : ℕ}
    (hf : IsHomogeneousPolynomial f n) (c : ℝ) :
    IsHomogeneousPolynomial (fun x => c * f x) n := by
  obtain ⟨p, hp, hv⟩ := hf
  exact ⟨MvPolynomial.C c * p, hp.C_mul c, fun x => by simp [hv]⟩

-- @node: homogeneous_function_neg
/-- If [f is a homogeneous polynomial of degree n](hyp:hf), then
[its pointwise negative is homogeneous of degree n](goal). -/
lemma homogeneous_function_neg {f : E → ℝ} {n : ℕ}
    (hf : IsHomogeneousPolynomial f n) :
    IsHomogeneousPolynomial (fun x => -f x) n := by
  simpa using homogeneous_function_const_mul hf (-1)

-- @node: homogeneous_function_sum
/-- For [a finite index set s](hyp:s), [a family of real-valued functions f](hyp:f),
and [a common degree n](hyp:n), if [each function indexed by s is a homogeneous
polynomial of degree n](hyp:hf), then [their sum over s is homogeneous of degree n](goal). -/
lemma homogeneous_function_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℝ) (n : ℕ)
    (hf : ∀ i ∈ s, IsHomogeneousPolynomial (f i) n) :
    IsHomogeneousPolynomial (fun x => ∑ i ∈ s, f i x) n := by
  classical
  choose p hp hv using hf
  refine ⟨∑ i ∈ s, if h : i ∈ s then p i h else 0, ?_, ?_⟩
  · exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun i hi => by simp [hi, hp])
  · intro x
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi, hv]

-- @node: homogeneous_function_prod
/-- For [a finite index set s](hyp:s), [a family of real-valued functions f](hyp:f),
and [a common degree n](hyp:n), if [each function indexed by s is a homogeneous
polynomial of degree n](hyp:hf), then [their product over s is homogeneous of degree
equal to the number of indices in s times n](goal). -/
lemma homogeneous_function_prod {ι : Type*} (s : Finset ι) (f : ι → E → ℝ) (n : ℕ)
    (hf : ∀ i ∈ s, IsHomogeneousPolynomial (f i) n) :
    IsHomogeneousPolynomial (fun x => ∏ i ∈ s, f i x) (s.card * n) := by
  classical
  choose p hp hv using hf
  refine ⟨∏ i ∈ s, if h : i ∈ s then p i h else 1, ?_, ?_⟩
  · simpa using MvPolynomial.IsHomogeneous.prod s
      (fun i => if h : i ∈ s then p i h else 1) (fun _ => n)
      (fun i hi => by simp [hi, hp])
  · intro x
    simp only [map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    simp [hi, hv]

-- @node: homogeneous_matrix_det
/-- For [a square real matrix A depending on a vector](hyp:A) and [a degree d](hyp:d),
if [every entry of A is a homogeneous polynomial of degree d](hyp:hA), then
[its determinant is homogeneous of degree equal to the matrix size times d](goal). -/
lemma homogeneous_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : E → Matrix ι ι ℝ) (d : ℕ)
    (hA : ∀ i j, IsHomogeneousPolynomial (fun x => A x i j) d) :
    IsHomogeneousPolynomial (fun x => (A x).det) (Fintype.card ι * d) := by
  classical
  simp only [Matrix.det_apply']
  apply homogeneous_function_sum
  intro σ _
  apply homogeneous_function_const_mul
  simpa using homogeneous_function_prod Finset.univ (fun i x => A x (σ i) i) d
    (fun i _ => hA (σ i) i)

-- @node: homogeneous_matrix_adjugate
/-- For [a real 4-by-4 matrix A depending on a vector](hyp:A), if
[every entry of A is homogeneous of degree one](hyp:hA), then at
[any row i and column j](hyp:i,j), [the corresponding entry of the adjugate of A
is a homogeneous polynomial of degree three](goal). -/
lemma homogeneous_matrix_adjugate (A : E → Mat 4)
    (hA : ∀ i j, IsHomogeneousPolynomial (fun x => A x i j) 1) (i j : Fin 4) :
    IsHomogeneousPolynomial (fun x => (A x).adjugate i j) 3 := by
  simp only [Matrix.adjugate_fin_succ_eq_det_submatrix]
  apply homogeneous_function_const_mul
  simpa using homogeneous_matrix_det
    (fun x => (A x).submatrix j.succAbove i.succAbove) 1
    (fun k l => hA _ _)

end PolynomialOperations

end Papers.OaiExactSemidefiniteLift
