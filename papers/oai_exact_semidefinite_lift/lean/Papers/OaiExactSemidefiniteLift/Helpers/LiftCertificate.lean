module

public import Papers.OaiExactSemidefiniteLift.Helpers.Moment
public import Papers.OaiExactSemidefiniteLift.Helpers.Matching
public import Papers.OaiExactSemidefiniteLift.Helpers.CertificateAlgebra
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Scalar certificate and the singular boundary

The matching construction uses arbitrary symmetric D. Only the scalar polynomial
in z is extended by continuity; the matching function is never extended.
-/

@[expose] public section

noncomputable section

namespace Papers.OaiExactSemidefiniteLift

open Matrix
open scoped BigOperators

/-- For [symmetric four-by-four matrices X and Z](hyp:X,Z), [an output three-vector
y](hyp:y), [a test four-vector u](hyp:u), [a symmetric test matrix D](hyp:D), and
[a test three-vector z](hyp:z), the [scalar certificate](goal) is the quadratic
form of Z at u plus the trace of the product of the vector block map, D, X, D,
the transposed block map, and the quadratic matrix at z, minus twice the trace
pairing of the D-weighted block map with the polarization at y and z. -/
def scalarCertificate (X Z : Sym4) (y : Fin 3 → ℝ) (u : Fin 4 → ℝ)
    (D : Sym4) (z : Fin 3 → ℝ) : ℝ := -- @realizes D(arbitrary symmetric test matrix)
  dotProduct u ((Z : Mat 4).mulVec u) +
    (Ju u * (D : Mat 4) * (X : Mat 4) * (D : Mat 4) * (Ju u)ᵀ * Qmat z).trace -
    2 * (Ju u * (D : Mat 4) * (Ju u)ᵀ * Qpol y z).trace

/-- For [a four-vector u](hyp:u), [a symmetric four-by-four matrix D](hyp:D),
[a complex three-by-two matrix function C](hyp:C), [a coordinate among twenty](hyp:i),
and [an angle](hyp:θ), the [matching test coordinate](goal) is
[the corresponding entry of minus D times the transposed vector block map
applied to the appropriate realified column of C at that angle, in a top block](step:1),
or [the corresponding entry of u, in the bottom block](step:2). -/
def matchingTestVector (u : Fin 4 → ℝ) (D : Sym4)
    (C : ℝ → Matrix (Fin 3) (Fin 2) ℂ) (i : Fin 20) (θ : ℝ) : ℝ :=
  Sum.elim
    (fun ji : Fin 4 × Fin 4 => -((D : Mat 4) * (Ju u)ᵀ).mulVec
      (fun l => realify (C θ) l ji.1) ji.2)
    (fun j : Fin 4 => u j) (sliceIndexEquiv.symm i)

/-- For [a complex three-by-two matrix function](hyp:C) and [an angle](hyp:θ),
the [real matching matrix](goal) interleaves the real and imaginary columns of
the function's value at that angle. -/
def matchingRealC (C : ℝ → Matrix (Fin 3) (Fin 2) ℂ) (θ : ℝ) :=
  -- @realizes \widetilde C(\theta)(realification of the chosen matching function)
  realify (C θ)

/-- For [a complex three-by-two matrix function](hyp:C), [one of four realified
column indices](hyp:j), and [an angle](hyp:θ), the [matching column](goal) is
that column of the realification of the function's value at the angle. -/
def matchingColumn (C : ℝ → Matrix (Fin 3) (Fin 2) ℂ) (j : Fin 4)
    (θ : ℝ) : Fin 3 → ℝ := -- @realizes b_j(real columns of the matching function)
  fun l => realify (C θ) l j

-- @node: complexTrig_two_parts
/-- If [a complex-valued function is a trigonometric polynomial of degree at
most two](hyp:hf), then [its real and imaginary parts are both real
trigonometric polynomials of degree at most two](goal). -/
lemma complexTrig_two_parts (f : ℝ → ℂ) (hf : IsComplexTrigPolyLE 2 f) :
    IsTrigPolyLE 2 (fun θ => (f θ).re) ∧ IsTrigPolyLE 2 (fun θ => (f θ).im) := by
  rcases hf with ⟨c, hc⟩
  have hi : Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} := by decide
  constructor
  · apply (momentBasis_spans _).2
    refine ⟨![(c 0).re, (c 1).re + (c (-1)).re, (c (-1)).im - (c 1).im,
      (c 2).re + (c (-2)).re, (c (-2)).im - (c 2).im], ?_⟩
    intro θ
    rw [hc θ]
    norm_num [hi, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Complex.mul_re, Complex.mul_im, Fin.sum_univ_succ, momentBasis,
      show (-2 : ℂ) * (θ : ℂ) = ((-(2 * θ) : ℝ) : ℂ) by push_cast; ring]
    <;> rw [show (2 : ℂ) * θ = ((2 * θ : ℝ) : ℂ) by push_cast; rfl]
    <;> simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero, zero_add, neg_zero]
    <;> ring
  · apply (momentBasis_spans _).2
    refine ⟨![(c 0).im, (c 1).im + (c (-1)).im, (c 1).re - (c (-1)).re,
      (c 2).im + (c (-2)).im, (c 2).re - (c (-2)).re], ?_⟩
    intro θ
    rw [hc θ]
    norm_num [hi, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Complex.mul_re, Complex.mul_im, Fin.sum_univ_succ, momentBasis,
      show (-2 : ℂ) * (θ : ℂ) = ((-(2 * θ) : ℝ) : ℂ) by push_cast; ring]
    <;> rw [show (2 : ℂ) * θ = ((2 * θ : ℝ) : ℂ) by push_cast; rfl]
    <;> simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero, zero_add, neg_zero]
    <;> ring

-- @node: matching_test_trig
/-- If [every entry of the complex matching matrix function is a trigonometric
polynomial of degree at most two](hyp:hC), then [each coordinate of the matching
test vector is a real trigonometric polynomial of degree at most two](goal). -/
lemma matching_test_trig (u : Fin 4 → ℝ) (D : Sym4)
    (C : ℝ → Matrix (Fin 3) (Fin 2) ℂ)
    (hC : ∀ i j, IsComplexTrigPolyLE 2 (fun θ => C θ i j)) (i : Fin 20) :
    IsTrigPolyLE 2 (matchingTestVector u D C i) := by
  have hreal (l : Fin 3) (j : Fin 4) :
      IsTrigPolyLE 2 (fun θ => realify (C θ) l j) := by
    fin_cases j
    · exact (complexTrig_two_parts _ (hC l 0)).1
    · exact (complexTrig_two_parts _ (hC l 0)).2
    · exact (complexTrig_two_parts _ (hC l 1)).1
    · exact (complexTrig_two_parts _ (hC l 1)).2
  obtain ⟨ji, hi⟩ := sliceIndexEquiv.surjective i
  subst i
  unfold matchingTestVector
  simp only [Equiv.symm_apply_apply]
  cases ji with
  | inl ji =>
    choose t ht using fun l => (momentBasis_spans _).1 (hreal l ji.1)
    apply (momentBasis_spans _).2
    refine ⟨fun b => -∑ l : Fin 3, ((D : Mat 4) * (Ju u)ᵀ) ji.2 l * t l b, ?_⟩
    intro θ
    simp only [Sum.elim_inl, Matrix.mulVec, dotProduct, ht, Finset.mul_sum, neg_mul,
      ← Finset.sum_neg_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  | inr j =>
    exact Causalean.Mathlib.Analysis.BernsteinSzegoTrig.isTrigPolyLE_const 2 (u j)

-- @node: topBlockTestVector
/-- For [a four-vector u](hyp:u), [a coordinate among twenty](hyp:i), and
[a real angle](hyp:_), the [top-block test coordinate](goal), independent of that angle, is
[the corresponding entry of u in the first top block and zero in the other top
blocks](step:1), and [zero in the bottom block](step:2). -/
def topBlockTestVector (u : Fin 4 → ℝ) (i : Fin 20) (_ : ℝ) : ℝ :=
  Sum.elim (fun ji : Fin 4 × Fin 4 => if ji.1 = 0 then u ji.2 else 0)
    (fun _ => 0) (sliceIndexEquiv.symm i)

-- @node: topBlockTestVector_quadratic
/-- [Evaluating the coordinate pencil's quadratic form on the test vector
supported in its first top block gives exactly the quadratic form of the
extracted X block at the original four-vector](goal). -/
lemma topBlockTestVector_quadratic (u : Fin 4 → ℝ) (θ : ℝ) (x : Fin 22 → ℝ) :
    (∑ i : Fin 20, ∑ j : Fin 20,
      topBlockTestVector u i θ * pencilFromCoords θ x i j * topBlockTestVector u j θ) =
      ∑ i : Fin 4, ∑ j : Fin 4, u i * sliceRawX x i j * u j := by
  rw [← sliceIndexEquiv.sum_comp]
  simp_rw [← sliceIndexEquiv.sum_comp]
  simp [topBlockTestVector, pencilFromCoords, slicePencilRaw,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Matrix.fromBlocks,
    Matrix.one_apply]

-- @node: topBlockTestVector_elem
/-- [The lift-space quadratic element for the first-top-block test vector is
the sum of the X-coordinate elements weighted by the pairwise products of the
test vector's coordinates](goal). -/
lemma topBlockTestVector_elem (u : Fin 4 → ℝ) :
    quadraticFunctionElem (topBlockTestVector u) =
      ∑ i : Fin 4, ∑ j : Fin 4, (u i * u j) • coordXElem i j := by
  ext c k
  simp only [quadraticFunctionElem, coordXElem, coefficientsOf,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, topBlockTestVector_quadratic]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 15)))]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro n _
  ring

-- @node: feasible_X_posSemidef
/-- If [the lift functional satisfies the output equations for X, Z, and y](hyp:hout)
and [is nonnegative on the admissible quadratic test elements](hyp:hm), then
[X is positive semidefinite](goal). -/
lemma feasible_X_posSemidef (Λ : LiftFunctional) (X Z : Sym4) (y : Fin 3 → ℝ)
    (hout : OutputEquations Λ X Z y) (hm : MomentPositive Λ) :
    (X : Mat 4).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨X.property, ?_⟩
  intro u
  have h := hm (topBlockTestVector u) (fun i =>
    Causalean.Mathlib.Analysis.BernsteinSzegoTrig.isTrigPolyLE_const 2
      (topBlockTestVector u i 0))
  rw [topBlockTestVector_elem] at h
  simpa [map_sum, map_smul, hout.1, dotProduct, Matrix.mulVec,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h

-- @node: scalarCertificate_coordinates
/-- [The scalar certificate expands in output coordinates as the sum of Z's
entries weighted by pairwise products of u's coordinates, plus X's entries
weighted by the corresponding entries of D times the transposed vector block
map times the quadratic matrix at z times the block map times D, minus twice
the sum of y's coordinates weighted by the trace pairings of the D-weighted
block map with the polarization of each coordinate unit vector and z](goal). -/
lemma scalarCertificate_coordinates (X Z : Sym4) (y : Fin 3 → ℝ)
    (u : Fin 4 → ℝ) (D : Sym4) (z : Fin 3 → ℝ) :
    scalarCertificate X Z y u D z =
      (∑ i : Fin 4, ∑ j : Fin 4, (u i * u j) * (Z : Mat 4) i j) +
      (∑ i : Fin 4, ∑ j : Fin 4,
        (((D : Mat 4) * (Ju u)ᵀ * Qmat z) * (Ju u * (D : Mat 4))) j i *
          (X : Mat 4) i j) -
      2 * ∑ l : Fin 3, ((Ju u * (D : Mat 4) * (Ju u)ᵀ *
        Qpol (Pi.single l 1) z).trace) * y l := by
  unfold scalarCertificate
  have ht := trace_sandwich_entries (Ju u * (D : Mat 4)) (X : Mat 4)
    ((D : Mat 4) * (Ju u)ᵀ * Qmat z)
  simp only [Matrix.mul_assoc] at ht
  rw [show (Ju u * (D : Mat 4) * (X : Mat 4) * (D : Mat 4) * (Ju u)ᵀ * Qmat z).trace =
    ∑ i : Fin 4, ∑ j : Fin 4,
      (((D : Mat 4) * (Ju u)ᵀ * Qmat z) * (Ju u * (D : Mat 4))) j i *
        (X : Mat 4) i j by simpa only [Matrix.mul_assoc] using ht,
    Qpol_left_coordinates y z]
  simp [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- For [a four-vector u](hyp:u) and [a symmetric four-by-four matrix D](hyp:D),
the [symmetric certificate weight](goal) is the vector block map associated
with u times D times the transpose of that block map. -/
def certificateWeight (u : Fin 4 → ℝ) (D : Sym4) : Sym3 :=
  -- @realizes S(symmetric weight J_u D J_uᵀ for arbitrary symmetric D)
  ⟨Ju u * (D : Mat 4) * (Ju u)ᵀ, by
    apply Matrix.isHermitian_iff_isSymm.mpr
    have hD := (Matrix.isHermitian_iff_isSymm.mp D.property).eq
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose, hD,
      Matrix.mul_assoc]⟩

-- @node: matchingTestVector_quadratic
/-- Suppose [the realified matching matrix has row Gram matrix equal to the
quadratic matrix at z at every angle](hyp:hgram), and [its weighted pairing
with the angular factor equals the trace pairing of the certificate weight
with the polarization at the angular-plane vector and z for every angle and
pair of plane coefficients](hyp:hpair). Then [the slice pencil's quadratic
form at the matching test vector equals the scalar certificate at that
angular-plane vector](goal). -/
lemma matchingTestVector_quadratic (X Z D : Sym4) (u : Fin 4 → ℝ)
    (z : Fin 3 → ℝ) (C : ℝ → Matrix (Fin 3) (Fin 2) ℂ)
    (hgram : ∀ θ, realify (C θ) * (realify (C θ))ᵀ = Qmat z)
    (hpair : ∀ θ η ξ, weightedPairing (certificateWeight u D)
      (Fθ θ η ξ) (C θ) =
        (Ju u * (D : Mat 4) * (Ju u)ᵀ * Qpol (Yplane θ η ξ) z).trace)
    (θ η ξ : ℝ) :
    (∑ i : Fin 20, ∑ j : Fin 20, matchingTestVector u D C i θ *
      slicePencil20 θ X Z η ξ i j * matchingTestVector u D C j θ) =
        scalarCertificate X Z (Yplane θ η ξ) u D z := by
  rw [← sliceIndexEquiv.sum_comp]
  simp_rw [← sliceIndexEquiv.sum_comp]
  simp only [matchingTestVector, slicePencil20, Equiv.symm_apply_apply]
  have h := slice_quadratic_expansion X Z θ η ξ
    (fun j => -((D : Mat 4) * (Ju u)ᵀ).mulVec (fun i => realify (C θ) i j)) u
  have hq : (∑ i : SliceIndex, ∑ j : SliceIndex,
      Sum.elim (fun ji => -((D : Mat 4) * (Ju u)ᵀ).mulVec
        (fun l => realify (C θ) l ji.1) ji.2) u i *
      slicePencil θ X Z η ξ i j *
      Sum.elim (fun ji => -((D : Mat 4) * (Ju u)ᵀ).mulVec
        (fun l => realify (C θ) l ji.1) ji.2) u j) =
      (∑ j : Fin 4, dotProduct (-((D : Mat 4) * (Ju u)ᵀ).mulVec
        (fun i => realify (C θ) i j)) ((X : Mat 4).mulVec
          (-((D : Mat 4) * (Ju u)ᵀ).mulVec (fun i => realify (C θ) i j)))) +
      2 * (∑ j : Fin 4, dotProduct (-((D : Mat 4) * (Ju u)ᵀ).mulVec
        (fun i => realify (C θ) i j)) ((Bskew (factorColumn θ η ξ j)).mulVec u)) +
      dotProduct u ((Z : Mat 4).mulVec u) := by
    simpa only [dotProduct, Matrix.mulVec, Pi.neg_apply, Finset.mul_sum, mul_assoc] using h
  rw [hq]
  simp_rw [certificate_top_column, certificate_cross_column]
  rw [trace_columns_quadratic, hgram θ, Finset.sum_neg_distrib]
  have hcross : (∑ j : Fin 4, dotProduct (factorColumn θ η ξ j)
      ((Ju u * (D : Mat 4) * (Ju u)ᵀ).mulVec (fun i => realify (C θ) i j))) =
      weightedPairing (certificateWeight u D) (Fθ θ η ξ) (C θ) := by
    exact trace_columns_pairing _ (realify (Fθ θ η ξ)) (realify (C θ))
  rw [hcross, hpair θ η ξ]
  unfold scalarCertificate
  ring

-- @node: feasible_certificate_nondegenerate
/-- If [the lift functional satisfies the output equations for X, Z, and y](hyp:hout),
[is nonnegative on admissible quadratic test elements](hyp:hm), and [the planar
part of the test three-vector is nonzero](hyp:hz), then [the scalar certificate
is nonnegative for every four-vector and symmetric test matrix](goal). -/
lemma feasible_certificate_nondegenerate (Λ : LiftFunctional)
    (X Z : Sym4) (y : Fin 3 → ℝ) (hout : OutputEquations Λ X Z y)
    (hm : MomentPositive Λ) (u : Fin 4 → ℝ) (D : Sym4) (z : Fin 3 → ℝ)
    (hz : MatchingNondegenerate z) :
    0 ≤ scalarCertificate X Z y u D z := by
  let S : Sym3 := certificateWeight u D
  obtain ⟨C, hdegree, hC⟩ := matching_exists S z hz
  have hgram (θ : ℝ) := (hC θ 0 0).1
  have hpair (θ η ξ : ℝ) := (hC θ η ξ).2
  let q := matchingTestVector u D C
  have hq := matching_test_trig u D C hdegree
  have helem : quadraticFunctionElem q =
      (∑ i : Fin 4, ∑ j : Fin 4, (u i * u j) • coordZElem i j) +
      (∑ i : Fin 4, ∑ j : Fin 4,
        (((D : Mat 4) * (Ju u)ᵀ * Qmat z) * (Ju u * (D : Mat 4))) j i •
          coordXElem i j) -
      (2 : ℝ) • ∑ l : Fin 3, (Ju u * (D : Mat 4) * (Ju u)ᵀ *
        Qpol (Pi.single l 1) z).trace • YplaneElem l := by
    apply evalLift_injective
    funext θ A B η ξ
    change evaluationFunctional θ A B η ξ _ = evaluationFunctional θ A B η ξ _
    simp only [map_sub, map_add, map_sum, map_smul, smul_eq_mul,
      evaluationFunctional, LinearMap.coe_mk, AddHom.coe_mk,
      eval_coordXElem, eval_coordZElem, eval_YplaneElem]
    rw [eval_quadraticFunctionElem q hq]
    exact (matchingTestVector_quadratic A B D u z C hgram hpair θ η ξ).trans
      (scalarCertificate_coordinates A B (Yplane θ η ξ) u D z)
  have h := hm q hq
  rw [helem] at h
  simp only [map_sub, map_add, map_sum, map_smul, smul_eq_mul,
    hout.1, hout.2.1, hout.2.2] at h
  rw [scalarCertificate_coordinates]
  exact h

-- @node: scalarCertificate_continuous
/-- [For fixed output matrices, output three-vector, test four-vector, and
symmetric test matrix, the scalar certificate is continuous in its test
three-vector](goal). -/
@[fun_prop]
lemma scalarCertificate_continuous (X Z : Sym4) (y : Fin 3 → ℝ)
    (u : Fin 4 → ℝ) (D : Sym4) :
    Continuous (scalarCertificate X Z y u D) := by
  have hQ : ∀ i j, Continuous (fun z => Qmat z i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Qmat] <;> fun_prop
  have hpol : ∀ i j, Continuous (fun z => Qpol y z i j) := by
    intro i j
    simp only [Qpol, QuadraticMap.polar, Matrix.smul_apply, Matrix.sub_apply]
    fun_prop
  unfold scalarCertificate
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  fun_prop

-- @node: feasible_certificate
/-- If [the lift functional satisfies the output equations for X, Z, and y](hyp:hout)
and [is nonnegative on admissible quadratic test elements](hyp:hm), then [the
scalar certificate is nonnegative for every test four-vector, symmetric test
matrix, and test three-vector, including those with zero planar part](goal). -/
lemma feasible_certificate (Λ : LiftFunctional) (X Z : Sym4) (y : Fin 3 → ℝ)
    (hout : OutputEquations Λ X Z y) (hm : MomentPositive Λ)
    (u : Fin 4 → ℝ) (D : Sym4) (z : Fin 3 → ℝ) :
    0 ≤ scalarCertificate X Z y u D z := by
  have hcont : Continuous (fun t : ℝ => scalarCertificate X Z y u D
      (Function.update z 0 t)) := by
    fun_prop
  have htest : ∀ t ∈ ({0}ᶜ : Set ℝ),
      0 ≤ scalarCertificate X Z y u D (Function.update z 0 t) := by
    intro t ht
    apply feasible_certificate_nondegenerate Λ X Z y hout hm u D
    intro heq
    have ht0 : t = 0 := by
      simpa using congrArg Prod.fst heq
    exact ht ht0
  have hmem : z 0 ∈ closure ({0}ᶜ : Set ℝ) := dense_compl_singleton 0 (z 0)
  simpa using le_on_closure htest continuous_const.continuousOn hcont.continuousOn hmem

-- @node: psd_pseudoinverse_exists
/-- If [X is positive semidefinite](hyp:hX), then [there exists a symmetric
positive semidefinite generalized inverse such that X times the inverse times
X equals X, the inverse times X times the inverse equals the inverse, and X
times the inverse is symmetric](goal). -/
lemma psd_pseudoinverse_exists (X : Sym4) (hX : (X : Mat 4).PosSemidef) :
    ∃ Xdagger : Sym4,
    -- @realizes X^\dagger(symmetric pseudoinverse, obtained from positive eigenspaces)
      (Xdagger : Mat 4).PosSemidef ∧
      (X : Mat 4) * (Xdagger : Mat 4) * (X : Mat 4) = (X : Mat 4) ∧
      (Xdagger : Mat 4) * (X : Mat 4) * (Xdagger : Mat 4) = (Xdagger : Mat 4) ∧
      ((X : Mat 4) * (Xdagger : Mat 4)).IsSymm := by
  let d := hX.isHermitian.eigenvalues
  let E := Unitary.conjStarAlgAut ℝ (Mat 4) hX.isHermitian.eigenvectorUnitary
  let T : Mat 4 := Matrix.diagonal (fun i => (d i)⁻¹)
  have hT : T.PosSemidef := Matrix.PosSemidef.diagonal
    (fun i => inv_nonneg.mpr (hX.eigenvalues_nonneg i))
  have hET : (E T).PosSemidef := by
    simpa only [E, Unitary.conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose] using
      hT.mul_mul_conjTranspose_same (hX.isHermitian.eigenvectorUnitary : Mat 4)
  have hXeq : (X : Mat 4) = E (Matrix.diagonal d) := by
    simpa only [E, d, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hX.isHermitian.spectral_theorem
  refine ⟨⟨E T, hET.isHermitian⟩, hET, ?_, ?_, ?_⟩
  · change (X : Mat 4) * E T * (X : Mat 4) = (X : Mat 4)
    rw [hXeq, ← map_mul, ← map_mul]
    congr 1
    simp only [T, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_inv_mul_cancel (d i)
  · change E T * (X : Mat 4) * E T = E T
    rw [hXeq, ← map_mul, ← map_mul]
    congr 1
    simp only [T, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simpa only [inv_inv] using mul_inv_mul_cancel ((d i)⁻¹)
  · change ((X : Mat 4) * E T).IsSymm
    rw [hXeq, ← map_mul]
    apply Matrix.isHermitian_iff_isSymm.mp
    have hd : (Matrix.diagonal d * T).IsHermitian := by
      simp only [T, Matrix.diagonal_mul_diagonal]
      exact Matrix.isHermitian_diagonal_of_self_adjoint _ (IsSelfAdjoint.all _)
    apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
    exact hd.isSelfAdjoint.map E


-- @node: rankOneSym
/-- For [a real four-vector v](hyp:v), the [symmetric outer-product matrix](goal)
has each entry equal to the product of the corresponding two coordinates of v. -/
def rankOneSym (v : Fin 4 → ℝ) : Sym4 :=
  ⟨Matrix.vecMulVec v v, by
    apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    intro i j
    exact mul_comm _ _⟩

-- @node: Qpol_self
/-- [Evaluating the bilinear polarization twice at the same three-vector
recovers the quadratic matrix at that vector](goal). -/
lemma Qpol_self (y : Fin 3 → ℝ) : Qpol y y = Qmat y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qpol, QuadraticMap.polar, Qmat] <;> ring

-- @node: rankOne_phi_gram
/-- [The quadratic form of the matrix map at an angular-plane vector, tested
on u with the outer-product matrix of v, equals the sum over the four real
factor columns of the squared inner products of v with the corresponding
skew block applied to u](goal). -/
lemma rankOne_phi_gram (θ η ξ : ℝ) (u v : Fin 4 → ℝ) :
    phiQuadraticForm (Yplane θ η ξ) u (rankOneSym v : Mat 4) =
      ∑ j : Fin 4, (dotProduct v ((Bskew (factorColumn θ η ξ j)).mulVec u)) ^ 2 := by
  rw [← phiQuadraticForm_eq, ← phiFactorSum_eq_PhiMap]
  unfold phiFactorSum
  simp only [Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec]
  simp only [rankOneSym, Matrix.vecMulVec_mulVec, smul_dotProduct,
    op_smul_eq_smul, smul_eq_mul, pow_two]

-- @node: scalarCertificate_rankOne_kernel
/-- If [v lies in the kernel of X](hyp:hv), then [the scalar certificate with
test matrix equal to a scalar times the outer product of v and test three-vector
equal to y reduces to the quadratic form of Z at u minus twice that scalar
times the matrix-map quadratic form at y, u, and the outer product of v](goal). -/
lemma scalarCertificate_rankOne_kernel (X Z : Sym4) (y : Fin 3 → ℝ)
    (u v : Fin 4 → ℝ) (hv : (X : Mat 4).mulVec v = 0) (t : ℝ) :
    scalarCertificate X Z y u (t • rankOneSym v) y =
      dotProduct u ((Z : Mat 4).mulVec u) -
        2 * t * phiQuadraticForm y u (rankOneSym v : Mat 4) := by
  have hzero : (X : Mat 4) * (rankOneSym v : Mat 4) = 0 := by
    simp [rankOneSym, Matrix.mul_vecMulVec, hv]
  have hprod : (t • (rankOneSym v : Mat 4)) * (X : Mat 4) *
      (t • (rankOneSym v : Mat 4)) = 0 := by
    rw [Matrix.mul_assoc, Matrix.mul_smul, hzero, smul_zero, Matrix.mul_zero]
  unfold scalarCertificate phiQuadraticForm
  simp only [SetLike.val_smul, Qpol_self]
  rw [Matrix.mul_assoc (Ju u) (t • (rankOneSym v : Mat 4)) (X : Mat 4),
    Matrix.mul_assoc (Ju u) ((t • (rankOneSym v : Mat 4)) * (X : Mat 4))
      (t • (rankOneSym v : Mat 4)), hprod]
  simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, mul_assoc]

-- @node: certificate_range
/-- If [X is positive semidefinite](hyp:hX), [all scalar certificates at the
angular-plane output vector are nonnegative](hyp:hc), and [v lies in the kernel
of X](hyp:hv), then [v is orthogonal to the image of any four-vector under each
skew block associated with a real angular-factor column](goal). -/
lemma certificate_range (X Z : Sym4) (θ η ξ : ℝ)
    (hX : (X : Mat 4).PosSemidef)
    (hc : ∀ (u : Fin 4 → ℝ) (D : Sym4) (z : Fin 3 → ℝ),
      0 ≤ scalarCertificate X Z (Yplane θ η ξ) u D z)
    (j : Fin 4) (v : Fin 4 → ℝ) (hv : (X : Mat 4).mulVec v = 0)
    (u : Fin 4 → ℝ) :
    dotProduct v ((Bskew (factorColumn θ η ξ j)).mulVec u) = 0 := by
  let a := phiQuadraticForm (Yplane θ η ξ) u (rankOneSym v : Mat 4)
  let b := dotProduct u ((Z : Mat 4).mulVec u)
  have ht (t : ℝ) : 0 ≤ b - 2 * t * a := by
    simpa only [scalarCertificate_rankOne_kernel X Z _ u v hv t] using
      hc u (t • rankOneSym v) (Yplane θ η ξ)
  have ha : a = 0 := by
    by_contra hne
    have h := ht ((b + 1) / (2 * a))
    have heq : 2 * ((b + 1) / (2 * a)) * a = b + 1 := by
      field_simp
    rw [heq] at h
    linarith
  have hsum : (∑ j : Fin 4,
      (dotProduct v ((Bskew (factorColumn θ η ξ j)).mulVec u)) ^ 2) = 0 := by
    rw [← rankOne_phi_gram]
    exact ha
  have hj : (dotProduct v ((Bskew (factorColumn θ η ξ j)).mulVec u)) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hsum j (by simp)
  exact sq_eq_zero_iff.mp hj

-- @node: certificate_projection
/-- Suppose [X is positive semidefinite](hyp:hX), [all scalar certificates at
the angular-plane output vector are nonnegative](hyp:hc), [X times P times X
equals X](hyp:hXPX), and [X times P is symmetric](hyp:hXP). Then [X times P fixes
the image of any four-vector under each skew block associated with a real
angular-factor column](goal). -/
lemma certificate_projection (X Z P : Sym4) (θ η ξ : ℝ)
    (hX : (X : Mat 4).PosSemidef)
    (hc : ∀ (u : Fin 4 → ℝ) (D : Sym4) (z : Fin 3 → ℝ),
      0 ≤ scalarCertificate X Z (Yplane θ η ξ) u D z)
    (hXPX : (X : Mat 4) * (P : Mat 4) * (X : Mat 4) = (X : Mat 4))
    (hXP : ((X : Mat 4) * (P : Mat 4)).IsSymm)
    (j : Fin 4) (u : Fin 4 → ℝ) :
    ((X : Mat 4) * (P : Mat 4)).mulVec
      ((Bskew (factorColumn θ η ξ j)).mulVec u) =
      (Bskew (factorColumn θ η ξ j)).mulVec u := by
  let b := (Bskew (factorColumn θ η ξ j)).mulVec u
  let v := b - ((X : Mat 4) * (P : Mat 4)).mulVec b
  have hsX : (X : Mat 4)ᵀ = (X : Mat 4) :=
    (Matrix.isHermitian_iff_isSymm.mp X.property).eq
  have hsP : (P : Mat 4)ᵀ = (P : Mat 4) :=
    (Matrix.isHermitian_iff_isSymm.mp P.property).eq
  have hcomm : (X : Mat 4) * (P : Mat 4) = (P : Mat 4) * (X : Mat 4) := by
    calc
      _ = ((X : Mat 4) * (P : Mat 4))ᵀ := hXP.eq.symm
      _ = _ := by rw [Matrix.transpose_mul, hsX, hsP]
  have hv : (X : Mat 4).mulVec v = 0 := by
    change (X : Mat 4).mulVec (b - ((X : Mat 4) * (P : Mat 4)).mulVec b) = 0
    rw [hcomm, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec b (X : Mat 4) ((P : Mat 4) * (X : Mat 4)),
      ← Matrix.mul_assoc, hXPX, sub_self]
  have hvb : dotProduct v b = 0 := certificate_range X Z θ η ξ hX hc j v hv u
  have hvX : dotProduct v (((X : Mat 4) * (P : Mat 4)).mulVec b) = 0 := by
    rw [← Matrix.mulVec_mulVec]
    rw [← hsX, Matrix.dotProduct_transpose_mulVec, hv, dotProduct_zero]
  have hvv : dotProduct v v = 0 := by
    change dotProduct v (b - _) = 0
    rw [dotProduct_sub, hvb, hvX, sub_self]
  have heq := dotProduct_self_eq_zero.mp hvv
  exact (sub_eq_zero.mp heq).symm

-- @node: certificate_slice_posSemidef
/-- If [X is positive semidefinite](hyp:hX) and [every scalar certificate at the
angular-plane output vector is nonnegative](hyp:hc), then [the corresponding
twenty-by-twenty slice pencil is positive semidefinite](goal). -/
lemma certificate_slice_posSemidef (X Z : Sym4) (θ η ξ : ℝ)
    (hX : (X : Mat 4).PosSemidef)
    (hc : ∀ (u : Fin 4 → ℝ) (D : Sym4) (z : Fin 3 → ℝ),
      0 ≤ scalarCertificate X Z (Yplane θ η ξ) u D z) :
    (slicePencil θ X Z η ξ).PosSemidef := by
  obtain ⟨P, hP, hXPX, hPXP, hXP⟩ := psd_pseudoinverse_exists X hX
  have hproj := certificate_projection X Z P θ η ξ hX hc hXPX hXP
  have hsX : (X : Mat 4)ᵀ = (X : Mat 4) :=
    (Matrix.isHermitian_iff_isSymm.mp X.property).eq
  have hsP : (P : Mat 4)ᵀ = (P : Mat 4) :=
    (Matrix.isHermitian_iff_isSymm.mp P.property).eq
  have hschur (u : Fin 4 → ℝ) :
      0 ≤ dotProduct u ((Z : Mat 4).mulVec u) -
        dotProduct u ((PhiMap (Yplane θ η ξ) (P : Mat 4)).mulVec u) := by
    have h := hc u P (Yplane θ η ξ)
    simp only [scalarCertificate, Qpol_self] at h
    rw [Matrix.mul_assoc (Ju u) (P : Mat 4) (X : Mat 4),
      Matrix.mul_assoc (Ju u) ((P : Mat 4) * (X : Mat 4)) (P : Mat 4), hPXP] at h
    have heq := phiQuadraticForm_eq (Yplane θ η ξ) u P
    dsimp only [phiQuadraticForm] at heq
    rw [← heq] at h
    linarith
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr (slicePencil_isSymm θ η ξ X Z), ?_⟩
  intro w
  let a : Fin 4 → Fin 4 → ℝ := fun j i => w (Sum.inl (j, i))
  let u : Fin 4 → ℝ := fun i => w (Sum.inr i)
  have hw : w = Sum.elim (fun ji => a ji.1 ji.2) u := by
    funext i
    cases i <;> rfl
  rw [show star w = w by simp, hw, slice_quadratic_expansion]
  have hterm (j : Fin 4) :
      0 ≤ dotProduct (a j) ((X : Mat 4).mulVec (a j)) +
        2 * dotProduct (a j) ((Bskew (factorColumn θ η ξ j)).mulVec u) +
        dotProduct u (((Bskew (factorColumn θ η ξ j))ᵀ * (P : Mat 4) *
          Bskew (factorColumn θ η ξ j)).mulVec u) := by
    let b := (Bskew (factorColumn θ η ξ j)).mulVec u
    have hpr : (X : Mat 4).mulVec ((P : Mat 4).mulVec b) = b := by
      rw [Matrix.mulVec_mulVec]
      exact hproj j u
    have hcross : dotProduct ((P : Mat 4).mulVec b) ((X : Mat 4).mulVec (a j)) =
        dotProduct (a j) b := by
      rw [← hsX, Matrix.dotProduct_transpose_mulVec, hpr]
    have hlast : dotProduct u (((Bskew (factorColumn θ η ξ j))ᵀ * (P : Mat 4) *
        Bskew (factorColumn θ η ξ j)).mulVec u) =
        dotProduct ((P : Mat 4).mulVec b) b := by
      simp only [← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_transpose_mulVec]
    have hnonneg := hX.dotProduct_mulVec_nonneg (a j + (P : Mat 4).mulVec b)
    simp only [star_trivial, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
      hpr, hcross] at hnonneg
    rw [hlast]
    change 0 ≤ dotProduct (a j) ((X : Mat 4).mulVec (a j)) +
      2 * dotProduct (a j) b + dotProduct ((P : Mat 4).mulVec b) b
    linarith
  have hsum := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) => hterm j)
  have hphi : dotProduct u ((PhiMap (Yplane θ η ξ) (P : Mat 4)).mulVec u) =
      ∑ j : Fin 4, dotProduct u (((Bskew (factorColumn θ η ξ j))ᵀ * (P : Mat 4) *
        Bskew (factorColumn θ η ξ j)).mulVec u) := by
    rw [← phiFactorSum_eq_PhiMap]
    simp only [phiFactorSum, Matrix.sum_mulVec, dotProduct_sum]
  have hrem := hschur u
  rw [hphi] at hrem
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  linarith

end Papers.OaiExactSemidefiniteLift
