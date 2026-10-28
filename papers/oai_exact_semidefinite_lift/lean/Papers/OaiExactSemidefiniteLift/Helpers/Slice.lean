module

public import Papers.OaiExactSemidefiniteLift.Helpers.Gram
public import Papers.OaiExactSemidefiniteLift.Helpers.Polynomial
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.Matrix.Order

/-!
# The factor identities and angular slice equivalence

Positive definiteness is used only for the inverse-matrix conclusion. The
principal slice equivalence covers every symmetric matrix, including singular ones.
-/

@[expose] public section

namespace Papers.OaiExactSemidefiniteLift

open Matrix

-- @node: PhiMap_entries
/-- For [a real three-vector y](hyp:y) and [a real 4-by-4 matrix W](hyp:W),
[Φᵧ(W) has upper-left entry given by the sum of Q(y)ᵢⱼWⱼ₊₁,ᵢ₊₁, upper-right
row −rᵀQ(y), lower-left column −Q(y)r, and lower-right block W₀₀Q(y),
where r consists of the last three entries of W's first column](goal). -/
lemma PhiMap_entries (y : Fin 3 → ℝ) (W : Mat 4) :
    PhiMap y W =
      !![(∑ i : Fin 3, ∑ j : Fin 3, Qmat y i j * W j.succ i.succ),
           (- ∑ l : Fin 3, W l.succ 0 * Qmat y l 0),
           (- ∑ l : Fin 3, W l.succ 0 * Qmat y l 1),
           (- ∑ l : Fin 3, W l.succ 0 * Qmat y l 2);
         (- ∑ l : Fin 3, Qmat y 0 l * W l.succ 0),
           W 0 0 * Qmat y 0 0, W 0 0 * Qmat y 0 1, W 0 0 * Qmat y 0 2;
         (- ∑ l : Fin 3, Qmat y 1 l * W l.succ 0),
           W 0 0 * Qmat y 1 0, W 0 0 * Qmat y 1 1, W 0 0 * Qmat y 1 2;
         (- ∑ l : Fin 3, Qmat y 2 l * W l.succ 0),
           W 0 0 * Qmat y 2 0, W 0 0 * Qmat y 2 1, W 0 0 * Qmat y 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

-- @node: Bskew_entries
/-- For [a real three-vector r](hyp:r), [the skew matrix B(r) has zero diagonal,
first row (0, r₀, r₁, r₂), first column (0, −r₀, −r₁, −r₂), and zero
lower-right 3-by-3 block](goal). -/
lemma Bskew_entries (r : Fin 3 → ℝ) :
    Bskew r = !![0, r 0, r 1, r 2;
      -r 0, 0, 0, 0; -r 1, 0, 0, 0; -r 2, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 800000 in
-- @node: phiFactorSum_eq_PhiMap
/-- For [an angle θ](hyp:θ), [plane coefficients η and ξ](hyp:η,ξ), and
[a symmetric real 4-by-4 matrix W](hyp:W), [the sum of BⱼᵀWBⱼ over the four
skew matrices formed from the real angular factor equals Φᵧ(W), where
y = η(cos θ, sin θ, 0) + ξ(0, 0, 1)](goal). -/
lemma phiFactorSum_eq_PhiMap (θ η ξ : ℝ) (W : Sym4) : -- @realizes W(symmetric four-by-four matrix)
    phiFactorSum θ η ξ (W : Mat 4) = PhiMap (Yplane θ η ξ) (W : Mat 4) := by
  have hW : (W : Mat 4).IsSymm := Matrix.isHermitian_iff_isSymm.mp W.property
  have hw (i j : Fin 4) : (W : Mat 4) j i = (W : Mat 4) i j := hW.apply i j
  rw [PhiMap_entries, ← gram_identity.1 θ η ξ]
  unfold phiFactorSum factorColumn
  generalize realify (Fθ θ η ξ) = F
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bskew_entries, Matrix.mul_apply, Fin.sum_univ_succ,
      hw 0 1, hw 0 2, hw 0 3, hw 1 2, hw 1 3, hw 2 3] <;> ring

-- The plan requires a def whose type asserts the identity.
set_option linter.defProp false in
/-- For [an angle θ](hyp:θ), [plane coefficients η and ξ](hyp:η,ξ), and
[a symmetric real 4-by-4 matrix W](hyp:W), [the factor identity](goal) certifies
that the sum of BⱼᵀWBⱼ over the four skew matrices from the real angular factor
equals Φᵧ(W), with y = η(cos θ, sin θ, 0) + ξ(0, 0, 1). -/
-- @node: def:phi-factor
def phiFactorIdentity (θ η ξ : ℝ) (W : Sym4) : -- @realizes W(symmetric matrix)
    phiFactorSum θ η ξ (W : Mat 4) = PhiMap (Yplane θ η ξ) (W : Mat 4) :=
  phiFactorSum_eq_PhiMap θ η ξ W

-- @node: phiQuadraticForm_eq
/-- For [a real three-vector y](hyp:y), [a real four-vector u](hyp:u), and
[a symmetric real 4-by-4 matrix W](hyp:W), [the quadratic form uᵀΦᵧ(W)u
equals the trace of JᵤWJᵤᵀQ(y), where Jᵤ has first column equal to the last
three coordinates of u and remaining block −u₀I](goal). -/
lemma phiQuadraticForm_eq (y : Fin 3 → ℝ) (u : Fin 4 → ℝ) (W : Sym4) :
    dotProduct u ((PhiMap y (W : Mat 4)).mulVec u) =
      phiQuadraticForm y u (W : Mat 4) := by
  have hW : (W : Mat 4).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp W.property
  have hw (i j : Fin 4) : (W : Mat 4) j i = (W : Mat 4) i j := hW.apply i j
  rw [PhiMap_entries]
  simp [phiQuadraticForm, Ju, Qmat, dotProduct, Matrix.mulVec,
    Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ,
    hw 0 1, hw 0 2, hw 0 3, hw 1 2, hw 1 3, hw 2 3]
  ring

-- The plan requires a def whose type asserts the identity.
set_option linter.defProp false in
/-- For [a real three-vector y](hyp:y), [a real four-vector u](hyp:u), and
[a symmetric real 4-by-4 matrix W](hyp:W), [the quadratic-form identity](goal)
certifies that uᵀΦᵧ(W)u equals the trace of JᵤWJᵤᵀQ(y), where Jᵤ has first
column equal to the last three coordinates of u and remaining block −u₀I. -/
-- @node: def:phi-quadratic
def phiQuadraticIdentity (y : Fin 3 → ℝ) (u : Fin 4 → ℝ)
    (W : Sym4) : -- @realizes W(symmetric matrix)
    dotProduct u ((PhiMap y (W : Mat 4)).mulVec u) =
      phiQuadraticForm y u (W : Mat 4) :=
  phiQuadraticForm_eq y u W

-- @node: PhiMap_isSymm
/-- For [a real three-vector y](hyp:y) and [a symmetric real 4-by-4 matrix W](hyp:W),
[the matrix Φᵧ(W) is symmetric](goal). -/
lemma PhiMap_isSymm (y : Fin 3 → ℝ) (W : Sym4) :
    (PhiMap y (W : Mat 4)).IsSymm := by
  rw [PhiMap_entries]
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Qmat, Fin.sum_univ_succ] <;> ring

-- @node: polynomial_X_coordinate
/-- For [any row i and column j of the first matrix X in an ambient triple
(X, Z, y)](hyp:i,j), [the entry Xᵢⱼ is a homogeneous polynomial of degree one
in the ambient triple](goal). -/
lemma polynomial_X_coordinate (i j : Fin 4) :
    Toolkit.Foundations.Algebra.IsHomogeneousPolynomial
      (fun x : V => (x.1 : Mat 4) i j) 1 := by
  exact homogeneous_linear_coordinate
    { toFun := fun x : V => (x.1 : Mat 4) i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

-- @node: polynomial_Z_coordinate
/-- For [any row i and column j of the second matrix Z in an ambient triple
(X, Z, y)](hyp:i,j), [the entry Zᵢⱼ is a homogeneous polynomial of degree one
in the ambient triple](goal). -/
lemma polynomial_Z_coordinate (i j : Fin 4) :
    Toolkit.Foundations.Algebra.IsHomogeneousPolynomial
      (fun x : V => (x.2.1 : Mat 4) i j) 1 := by
  exact homogeneous_linear_coordinate
    { toFun := fun x : V => (x.2.1 : Mat 4) i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

-- @node: polynomial_y_coordinate
/-- For [any coordinate i of the three-vector y in an ambient triple (X, Z, y)](hyp:i),
[the coordinate yᵢ is a homogeneous polynomial of degree one in the ambient triple](goal). -/
lemma polynomial_y_coordinate (i : Fin 3) :
    Toolkit.Foundations.Algebra.IsHomogeneousPolynomial
      (fun x : V => x.2.2 i) 1 := by
  exact homogeneous_linear_coordinate
    { toFun := fun x : V => x.2.2 i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

-- @node: polynomial_Q_coordinate
/-- For [any row i and column j of Q(y)](hyp:i,j), [the entry Q(y)ᵢⱼ is a
homogeneous polynomial of degree two in the ambient triple (X, Z, y)](goal). -/
lemma polynomial_Q_coordinate (i j : Fin 3) :
    Toolkit.Foundations.Algebra.IsHomogeneousPolynomial
      (fun x : V => Qmat x.2.2 i j) 2 := by
  have hmul (k l : Fin 3) :=
    homogeneous_function_mul (polynomial_y_coordinate k) (polynomial_y_coordinate l)
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Qmat, Matrix.of_apply,
      Matrix.cons_val_zero, pow_two, neg_mul]
  all_goals first
    | exact homogeneous_function_add (hmul _ _) (hmul _ _)
    | exact homogeneous_function_neg (hmul _ _)

-- @node: polynomial_Phi_adjugate_coordinate
/-- For [any row i and column j](hyp:i,j), [the corresponding entry of
Φᵧ(adj(X)) is a homogeneous polynomial of degree five in the ambient triple
(X, Z, y)](goal). -/
lemma polynomial_Phi_adjugate_coordinate (i j : Fin 4) :
    Toolkit.Foundations.Algebra.IsHomogeneousPolynomial
      (fun x : V => PhiMap x.2.2 (x.1 : Mat 4).adjugate i j) 5 := by
  have hW (k l : Fin 4) := homogeneous_matrix_adjugate
    (fun x : V => (x.1 : Mat 4)) polynomial_X_coordinate k l
  have hQ := polynomial_Q_coordinate
  simp_rw [PhiMap_entries]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Matrix.of_apply,
      Matrix.cons_val_zero]
  all_goals first
    | exact homogeneous_function_sum _ _ _ (fun k _ =>
        homogeneous_function_sum _ _ _ (fun l _ =>
          homogeneous_function_mul (hQ _ _) (hW _ _)))
    | exact homogeneous_function_neg (homogeneous_function_sum _ _ _ (fun k _ =>
        homogeneous_function_mul (hW _ _) (hQ _ _)))
    | exact homogeneous_function_neg (homogeneous_function_sum _ _ _ (fun k _ =>
        homogeneous_function_mul (hQ _ _) (hW _ _)))
    | exact homogeneous_function_mul (hW _ _) (hQ _ _)

-- @node: pPoly_homogeneous
/-- [The polynomial p(X, Z, y) = det(det(X)Z − Φᵧ(adj(X))) is homogeneous
of degree twenty in the ambient triple (X, Z, y)](goal). -/
lemma pPoly_homogeneous :
    Toolkit.Foundations.Algebra.IsHomogeneousPolynomial pPoly 20 := by
  have hdet := homogeneous_matrix_det (fun x : V => (x.1 : Mat 4)) 1
    polynomial_X_coordinate
  change Toolkit.Foundations.Algebra.IsHomogeneousPolynomial
    (fun x : V => ((x.1 : Mat 4).det • (x.2.1 : Mat 4) -
      PhiMap x.2.2 (x.1 : Mat 4).adjugate).det) (4 * 5)
  apply homogeneous_matrix_det _ 5
  intro i j
  exact homogeneous_function_sub
    (homogeneous_function_mul hdet (polynomial_Z_coordinate i j))
    (polynomial_Phi_adjugate_coordinate i j)

-- @node: pPoly_eDir
/-- [The determinant polynomial p takes the value one at the distinguished
direction (I, I, 0)](goal). -/
lemma pPoly_eDir : pPoly eDir = 1 := by
  have hzero : PhiMap (0 : Fin 3 → ℝ) (1 : Mat 4) = 0 := by
    rw [PhiMap_entries]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Qmat, Fin.sum_univ_succ]
  simp [pPoly, eDir, identity4, hzero]

-- @node: slicePencil_isSymm
/-- For [an angle θ](hyp:θ), [plane coefficients η and ξ](hyp:η,ξ), and
[symmetric real 4-by-4 matrices X and Z](hyp:𝒳,𝒵), [the associated 20-by-20
slice pencil is symmetric](goal). -/
lemma slicePencil_isSymm (θ η ξ : ℝ) (𝒳 𝒵 : Sym4) :
    (slicePencil θ 𝒳 𝒵 η ξ).IsSymm := by
  have hX : (𝒳 : Mat 4).IsSymm := Matrix.isHermitian_iff_isSymm.mp 𝒳.property
  have hZ : (𝒵 : Mat 4).IsSymm := Matrix.isHermitian_iff_isSymm.mp 𝒵.property
  apply Matrix.IsSymm.fromBlocks (B := sliceB θ η ξ) _ rfl hZ
  apply Matrix.IsSymm.ext
  intro i j
  simp [hX.apply i.2 j.2, Matrix.one_apply, eq_comm]

-- @node: slice_schur_factor
/-- For [an angle θ](hyp:θ), [plane coefficients η and ξ](hyp:η,ξ), and
[a symmetric real 4-by-4 matrix W](hyp:W), [multiplying the block diagonal
matrix with four copies of W on the left by the transpose of the stacked skew
factor and on the right by that factor gives Φᵧ(W), where
y = η(cos θ, sin θ, 0) + ξ(0, 0, 1)](goal). -/
lemma slice_schur_factor (θ η ξ : ℝ) (W : Sym4) :
    (sliceB θ η ξ)ᵀ * Matrix.kronecker (1 : Mat 4) (W : Mat 4) * sliceB θ η ξ =
      PhiMap (Yplane θ η ξ) (W : Mat 4) := by
  rw [← phiFactorSum_eq_PhiMap]
  ext i j
  simp [phiFactorSum, sliceB, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Finset.sum_mul, Finset.mul_sum, Matrix.sum_apply, mul_assoc]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]

-- @node: PhiMap_smul
/-- For [a real three-vector y](hyp:y), [a real scalar a](hyp:a), and
[a real 4-by-4 matrix W](hyp:W), [applying Φᵧ to aW gives a times Φᵧ(W)](goal). -/
lemma PhiMap_smul (y : Fin 3 → ℝ) (a : ℝ) (W : Mat 4) :
    PhiMap y (a • W) = a • PhiMap y W := by
  simp_rw [PhiMap_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ] <;> ring

-- @node: slice_determinant_of_isUnit
/-- For [an angle θ](hyp:θ), [plane coefficients η and ξ](hyp:η,ξ), and
[symmetric real 4-by-4 matrices X and Z](hyp:𝒳,𝒵), if [X is invertible](hyp:hX),
then [p(X, Z, y) equals the determinant of the slice pencil, where
y = η(cos θ, sin θ, 0) + ξ(0, 0, 1)](goal). -/
lemma slice_determinant_of_isUnit (θ η ξ : ℝ) (𝒳 𝒵 : Sym4)
    (hX : IsUnit (𝒳 : Mat 4)) :
    pPoly (𝒳, 𝒵, Yplane θ η ξ) = (slicePencil θ 𝒳 𝒵 η ξ).det := by
  let := hX.invertible
  have hA : IsUnit (Matrix.kronecker (1 : Mat 4) (𝒳 : Mat 4)) := by
    exact IsUnit.kronecker isUnit_one hX
  let := hA.invertible
  have hinv : (Matrix.kronecker (1 : Mat 4) (𝒳 : Mat 4))⁻¹ =
      Matrix.kronecker (1 : Mat 4) (𝒳 : Mat 4)⁻¹ := by
    simpa only [Matrix.kronecker, inv_one] using
      Matrix.inv_kronecker (1 : Mat 4) (𝒳 : Mat 4)
  have hadj : (𝒳 : Mat 4).adjugate = (𝒳 : Mat 4).det • (𝒳 : Mat 4)⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv, mul_inv_cancel₀, one_smul]
    exact (Matrix.isUnit_det_of_invertible (𝒳 : Mat 4)).ne_zero
  have hdet : (Matrix.kronecker (1 : Mat 4) (𝒳 : Mat 4)).det =
      (𝒳 : Mat 4).det ^ 4 := by
    simp [Matrix.kronecker, Matrix.det_kronecker]
  change _ = (Matrix.fromBlocks _ _ _ _).det
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, hinv,
    slice_schur_factor θ η ξ
      ⟨(𝒳 : Mat 4)⁻¹, (show (𝒳 : Mat 4).IsHermitian from 𝒳.property).inv⟩, hdet]
  unfold pPoly
  rw [hadj, PhiMap_smul, ← smul_sub, Matrix.det_smul]
  rfl

-- @node: slicePencil_shift
/-- For [an angle θ](hyp:θ), [plane coefficients η and ξ](hyp:η,ξ),
[a real shift t](hyp:t), and [symmetric real 4-by-4 matrices X and Z](hyp:𝒳,𝒵),
[the slice pencil evaluated at tI − X, tI − Z, −η, and −ξ equals t times
the 20-by-20 identity minus the original slice pencil](goal). -/
lemma slicePencil_shift (θ η ξ t : ℝ) (𝒳 𝒵 : Sym4) :
    slicePencil θ (t • identity4 - 𝒳) (t • identity4 - 𝒵) (-η) (-ξ) =
      t • (1 : Matrix SliceIndex SliceIndex ℝ) - slicePencil θ 𝒳 𝒵 η ξ := by
  have hF : realify (Fθ θ (-η) (-ξ)) = -realify (Fθ θ η ξ) := by
    rw [realify_Fθ_linear, realify_Fθ_linear]
    simp [neg_smul, add_comm]
  have hB : sliceB θ (-η) (-ξ) = -sliceB θ η ξ := by
    ext ⟨b, i⟩ j
    fin_cases i <;> fin_cases j <;>
      simp [sliceB, Bskew_entries, factorColumn, hF]
  ext i j
  cases i <;> cases j <;>
    simp [slicePencil, slicePencilRaw, hB, Matrix.one_apply,
      identity4, Matrix.kroneckerMap_apply, mul_sub, mul_ite, ite_mul] <;>
    try (split_ifs <;> simp_all [Prod.ext_iff])

-- @node: Yplane_neg
/-- For [an angle θ](hyp:θ) and [plane coefficients η and ξ](hyp:η,ξ),
[negating both coefficients negates the vector η(cos θ, sin θ, 0) + ξ(0, 0, 1)](goal). -/
lemma Yplane_neg (θ η ξ : ℝ) :
    Yplane θ (-η) (-ξ) = -Yplane θ η ξ := by
  simp [Yplane, neg_smul, add_comm]

-- @node: slice_determinant_identity
/-- For [an angle θ](hyp:θ), [plane coefficients η and ξ](hyp:η,ξ),
[a real scalar t](hyp:t), and [symmetric real 4-by-4 matrices X and Z](hyp:𝒳,𝒵),
[evaluating p at t(I, I, 0) − (X, Z, y) equals the determinant of tI minus
the slice pencil, where y = η(cos θ, sin θ, 0) + ξ(0, 0, 1)](goal). -/
lemma slice_determinant_identity (θ η ξ t : ℝ) (𝒳 𝒵 : Sym4) :
    pPoly (t • eDir - (𝒳, 𝒵, Yplane θ η ξ)) =
      (t • (1 : Matrix SliceIndex SliceIndex ℝ) - slicePencil θ 𝒳 𝒵 η ξ).det := by
  classical
  let f := Toolkit.Foundations.Algebra.characteristicPolynomial pPoly eDir
    (𝒳, 𝒵, Yplane θ η ξ)
  let g := (slicePencil θ 𝒳 𝒵 η ξ).charpoly
  -- The block determinant formula applies away from the finitely many roots of X.charpoly.
  have hgood (s : ℝ) (hs : IsUnit ((s • identity4 - 𝒳 : Sym4) : Mat 4)) :
      f.eval s = g.eval s := by
    have hv : s • eDir - (𝒳, 𝒵, Yplane θ η ξ) =
        (s • identity4 - 𝒳, s • identity4 - 𝒵, Yplane θ (-η) (-ξ)) := by
      rw [Yplane_neg]
      simp [eDir]
    dsimp [f, g]
    rw [Toolkit.Foundations.Algebra.eval_characteristicPolynomial pPoly_homogeneous,
      hv, slice_determinant_of_isUnit θ (-η) (-ξ) _ _ hs,
      slicePencil_shift, Matrix.eval_charpoly, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
  -- Polynomial equality on this infinite complement includes every singular value as well.
  have heq : f = g := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hfin := Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic (𝒳 : Mat 4)).ne_zero
    apply hfin.infinite_compl.mono
    intro s hs
    apply hgood
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    have hn : (𝒳 : Mat 4).charpoly.eval s ≠ 0 := hs
    simpa [Matrix.eval_charpoly, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, identity4] using hn
  have ht := congrArg (fun q : Polynomial ℝ => q.eval t) heq
  dsimp [f, g] at ht
  simpa only [Toolkit.Foundations.Algebra.eval_characteristicPolynomial pPoly_homogeneous,
    Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal] using ht

-- @node: slice_characteristicPolynomial
/-- For [an angle θ](hyp:θ), [plane coefficients η and ξ](hyp:η,ξ), and
[symmetric real 4-by-4 matrices X and Z](hyp:𝒳,𝒵), [the polynomial in t
given by p(t(I, I, 0) − (X, Z, y)) equals the characteristic polynomial of
the slice pencil, where y = η(cos θ, sin θ, 0) + ξ(0, 0, 1)](goal). -/
lemma slice_characteristicPolynomial (θ η ξ : ℝ) (𝒳 𝒵 : Sym4) :
    Toolkit.Foundations.Algebra.characteristicPolynomial pPoly eDir
      (𝒳, 𝒵, Yplane θ η ξ) = (slicePencil θ 𝒳 𝒵 η ξ).charpoly := by
  apply Polynomial.funext
  intro t
  rw [Toolkit.Foundations.Algebra.eval_characteristicPolynomial pPoly_homogeneous,
    slice_determinant_identity, Matrix.eval_charpoly]
  congr 2
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

-- @node: slice_cone_iff_posSemidef
/-- For [an angle θ](hyp:θ), [plane coefficients η and ξ](hyp:η,ξ), and
[symmetric real 4-by-4 matrices X and Z](hyp:𝒳,𝒵), [the triple (X, Z, y)
belongs to the closed hyperbolicity cone K if and only if its slice pencil
is positive semidefinite, where y = η(cos θ, sin θ, 0) + ξ(0, 0, 1)](goal). -/
lemma slice_cone_iff_posSemidef (θ η ξ : ℝ) (𝒳 𝒵 : Sym4) :
    (𝒳, 𝒵, Yplane θ η ξ) ∈ coneK ↔ (slicePencil θ 𝒳 𝒵 η ξ).PosSemidef := by
  classical
  have hA := Matrix.isHermitian_iff_isSymm.mpr (slicePencil_isSymm θ η ξ 𝒳 𝒵)
  change (∀ r : ℝ,
    (Toolkit.Foundations.Algebra.characteristicPolynomial pPoly eDir
      (𝒳, 𝒵, Yplane θ η ξ)).IsRoot r → 0 ≤ r) ↔ _
  rw [slice_characteristicPolynomial, hA.posSemidef_iff_eigenvalues_nonneg]
  constructor
  · intro h i
    apply h
    rw [Polynomial.IsRoot, hA.charpoly_eq]
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  · intro h r hr
    rw [Polynomial.IsRoot, hA.charpoly_eq] at hr
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] at hr
    obtain ⟨i, hi⟩ := hr
    rw [sub_eq_zero.mp hi]
    exact h i

-- @node: slice_posSemidef_iff_schur
/-- For [an angle θ](hyp:θ), [plane coefficients η and ξ](hyp:η,ξ), and
[symmetric real 4-by-4 matrices X and Z](hyp:𝒳,𝒵), if [X is positive definite](hyp:hX),
then [the slice pencil is positive semidefinite if and only if
Z − Φᵧ(X⁻¹) is positive semidefinite, where
y = η(cos θ, sin θ, 0) + ξ(0, 0, 1)](goal). -/
lemma slice_posSemidef_iff_schur (θ η ξ : ℝ) (𝒳 𝒵 : Sym4)
    (hX : SlicePosDef 𝒳) :
    (slicePencil θ 𝒳 𝒵 η ξ).PosSemidef ↔
      ((𝒵 : Mat 4) - PhiMap (Yplane θ η ξ) (𝒳 : Mat 4)⁻¹).PosSemidef := by
  have hA : (Matrix.kronecker (1 : Mat 4) (𝒳 : Mat 4)).PosDef :=
    Matrix.PosDef.kronecker Matrix.PosDef.one hX
  let := hA.isUnit.invertible
  change (Matrix.fromBlocks _ _ _ _).PosSemidef ↔ _
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial (sliceB θ η ξ),
    Matrix.PosDef.fromBlocks₁₁ _ _ hA]
  have hinv : (Matrix.kronecker (1 : Mat 4) (𝒳 : Mat 4))⁻¹ =
      Matrix.kronecker (1 : Mat 4) (𝒳 : Mat 4)⁻¹ := by
    simpa only [Matrix.kronecker, inv_one] using Matrix.inv_kronecker (1 : Mat 4) (𝒳 : Mat 4)
  rw [hinv, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [slice_schur_factor θ η ξ ⟨(𝒳 : Mat 4)⁻¹, hX.inv.1⟩]

-- @node: lem:slice
/-- [For every angle θ, plane coefficients η and ξ, and symmetric real 4-by-4
matrices X and Z, the triple (X, Z, y) belongs to K exactly when its slice
pencil is positive semidefinite; p is hyperbolic in direction (I, I, 0); and,
whenever X is positive definite, membership of (X, Z, y) in K is equivalent
to positive semidefiniteness of Z − Φᵧ(X⁻¹), where
y = η(cos θ, sin θ, 0) + ξ(0, 0, 1)](goal). -/
lemma slice_equivalence :
    (∀ (θ η ξ : ℝ) (𝒳 𝒵 : Sym4),
      (𝒳, 𝒵, Yplane θ η ξ) ∈ coneK ↔ (slicePencil θ 𝒳 𝒵 η ξ).PosSemidef) ∧
    Toolkit.Foundations.Algebra.IsHyperbolic pPoly eDir ∧
    (∀ (θ η ξ : ℝ) (𝒳 𝒵 : Sym4), SlicePosDef 𝒳 →
      ((𝒳, 𝒵, Yplane θ η ξ) ∈ coneK ↔
        ((𝒵 : Mat 4) - PhiMap (Yplane θ η ξ) (𝒳 : Mat 4)⁻¹).PosSemidef)) := by
  refine ⟨slice_cone_iff_posSemidef, ⟨?_, ?_⟩, ?_⟩
  · rw [pPoly_eDir]
    norm_num
  · intro x
    obtain ⟨θ, η, ξ, hy⟩ := angular_plane_surjective (-x).2.2
    have hx : -x = ((-x).1, (-x).2.1, Yplane θ η ξ) := by rw [← hy]
    have hs : (Toolkit.Foundations.Algebra.characteristicPolynomial pPoly eDir (-x)).Splits := by
      rw [hx, slice_characteristicPolynomial]
      exact (Matrix.isHermitian_iff_isSymm.mpr
        (slicePencil_isSymm θ η ξ (-x).1 (-x).2.1)).splits_charpoly
    simpa only [Toolkit.Foundations.Algebra.characteristicPolynomial, neg_neg] using hs
  · intro θ η ξ 𝒳 𝒵 hX
    exact (slice_cone_iff_posSemidef θ η ξ 𝒳 𝒵).trans
      (slice_posSemidef_iff_schur θ η ξ 𝒳 𝒵 hX)

end Papers.OaiExactSemidefiniteLift
