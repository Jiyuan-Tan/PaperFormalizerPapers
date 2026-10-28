module

public import Papers.OaiNearInclusionsVon.Helpers.NearReordering
public import Papers.OaiNearInclusionsVon.Helpers.LaurentUnitary

/-! Right-translation invariance and the reordered operator blocks. -/

public section

namespace Papers.OaiNearInclusionsVon

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

/-- For [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), and [an operator U on a finite-dimensional
Hilbert space](hyp:U) that [is unitary](hyp:hU), [the first substituted representation of the
product of two free-group elements g and h](hyp:g,h) [equals the product of their first
substituted representations, in the same order](goal). -/
-- @node: matrixRepA_mul
lemma matrixRepA_mul [FiniteDimensional ℂ D]
    (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U : D →L[ℂ] D) (hU : U ∈ unitary _) (g h : FreeGrp) :
    matrixRepA A U (g * h) = matrixRepA A U g * matrixRepA A U h := by
  apply lsp_ext_on_eigenvectors U hU
  intro z v hv x y
  rw [mul_apply_eq_comp, matrixRepA_tensorRight_eigen π A hπ U hU z v hv,
    matrixRepA_tensorRight_eigen π A hπ U hU z v hv,
    matrixRepA_tensorRight_eigen π A hπ U hU z v hv]
  rw [map_mul]
  rfl

/-- For [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), and [an operator U on a finite-dimensional
Hilbert space](hyp:U) that [is unitary](hyp:hU), [the second substituted representation of the
product of two free-group elements g and h](hyp:g,h) [equals the product of their second
substituted representations, in the same order](goal). -/
-- @node: matrixRepB_mul
lemma matrixRepB_mul [FiniteDimensional ℂ D]
    (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U : D →L[ℂ] D) (hU : U ∈ unitary _) (g h : FreeGrp) :
    matrixRepB A U (g * h) = matrixRepB A U g * matrixRepB A U h := by
  apply lsp_ext_on_eigenvectors U hU
  intro z v hv x y
  rw [mul_apply_eq_comp, matrixRepB_tensorRight_eigen π A hπ U hU z v hv,
    matrixRepB_tensorRight_eigen π A hπ U hU z v hv,
    matrixRepB_tensorRight_eigen π A hπ U hU z v hv]
  rw [map_mul]
  rfl

/-- For [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), and [an operator U on a finite-dimensional
Hilbert space](hyp:U) that [is unitary](hyp:hU), [the first substituted representation sends
the group identity to the identity operator](goal). -/
-- @node: matrixRepA_one
lemma matrixRepA_one [FiniteDimensional ℂ D]
    (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U : D →L[ℂ] D) (hU : U ∈ unitary _) : matrixRepA A U 1 = 1 := by
  apply lsp_ext_on_eigenvectors U hU
  intro z v hv x y
  rw [matrixRepA_tensorRight_eigen π A hπ U hU z v hv, map_one]
  rfl

/-- For [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), and [an operator U on a finite-dimensional
Hilbert space](hyp:U) that [is unitary](hyp:hU), [the second substituted representation sends
the group identity to the identity operator](goal). -/
-- @node: matrixRepB_one
lemma matrixRepB_one [FiniteDimensional ℂ D]
    (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U : D →L[ℂ] D) (hU : U ∈ unitary _) : matrixRepB A U 1 = 1 := by
  apply lsp_ext_on_eigenvectors U hU
  intro z v hv x y
  rw [matrixRepB_tensorRight_eigen π A hπ U hU z v hv, map_one]
  rfl

/-- For [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), and [an operator U on a finite-dimensional
Hilbert space](hyp:U) that [is unitary](hyp:hU), at [any free-group element g](hyp:g),
[the first substituted representation of the inverse of g is the adjoint of its value at g](goal). -/
-- @node: matrixRepA_inv
lemma matrixRepA_inv [FiniteDimensional ℂ D]
    (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U : D →L[ℂ] D) (hU : U ∈ unitary _) (g : FreeGrp) :
    matrixRepA A U g⁻¹ = star (matrixRepA A U g) := by
  have h := matrixRepA_mul π A hπ U hU g⁻¹ g
  rw [inv_mul_cancel, matrixRepA_one π A hπ U hU] at h
  calc
    matrixRepA A U g⁻¹ = matrixRepA A U g⁻¹ *
        (matrixRepA A U g * star (matrixRepA A U g)) := by
      rw [Unitary.mul_star_self_of_mem (matrixRepA_mem_unitary π A hπ U hU g), mul_one]
    _ = star (matrixRepA A U g) := by rw [← mul_assoc, ← h, one_mul]

/-- For [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), and [an operator U on a finite-dimensional
Hilbert space](hyp:U) that [is unitary](hyp:hU), at [any free-group element g](hyp:g),
[the second substituted representation of the inverse of g is the adjoint of its value at g](goal). -/
-- @node: matrixRepB_inv
lemma matrixRepB_inv [FiniteDimensional ℂ D]
    (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U : D →L[ℂ] D) (hU : U ∈ unitary _) (g : FreeGrp) :
    matrixRepB A U g⁻¹ = star (matrixRepB A U g) := by
  have h := matrixRepB_mul π A hπ U hU g⁻¹ g
  rw [inv_mul_cancel, matrixRepB_one π A hπ U hU] at h
  calc
    matrixRepB A U g⁻¹ = matrixRepB A U g⁻¹ *
        (matrixRepB A U g * star (matrixRepB A U g)) := by
      rw [Unitary.mul_star_self_of_mem (matrixRepB_mem_unitary π A hπ U hU g), mul_one]
    _ = star (matrixRepB A U g) := by rw [← mul_assoc, ← h, one_mul]

/-- For [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), take [operators U and V on a finite-dimensional
Hilbert space](hyp:U,V) with [U unitary](hyp:hU) and [V unitary](hyp:hV).
For [product-group elements x and y](hyp:x,y), [the product of the first substituted operator
at the first coordinate of x, the adjoint at the first coordinate of y, the second substituted
operator at the second coordinate of x, and the adjoint at the second coordinate of y equals
the product map at x times the inverse of y](goal). -/
-- @node: reordered_block_product
lemma reordered_block_product [FiniteDimensional ℂ D]
    (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U V : D →L[ℂ] D) (hU : U ∈ unitary _) (hV : V ∈ unitary _)
    (x y : ProdGrp) :
    matrixRepA A U x.1 * star (matrixRepA A U y.1) *
        (matrixRepB A V x.2 * star (matrixRepB A V y.2)) =
      prodMap A U V (x * y⁻¹) := by
  change _ = matrixRepA A U (x.1 * y.1⁻¹) * matrixRepB A V (x.2 * y.2⁻¹)
  rw [matrixRepA_mul π A hπ U hU, matrixRepB_mul π A hπ V hV,
    matrixRepA_inv π A hπ U hU, matrixRepB_inv π A hπ V hV]

/-- For [product-group elements q and y](hyp:q,y) and [a vector v in L](hyp:v),
[amplified right translation by q sends the sequence supported at y with value v to the
sequence supported at y times the inverse of q with the same value](goal). -/
-- @node: rhoAmp_single
lemma rhoAmp_single (q y : ProdGrp) (v : Lsp D) :
    rhoAmp q (lp.single 2 y v) = lp.single 2 (y * q⁻¹) v := by
  ext x
  simp only [rhoAmp, lpReindex_apply, Equiv.coe_mulRight, lp.single_apply]
  by_cases h : y = x * q
  · simp [h]
  · have h' : y * q⁻¹ ≠ x := by
      intro he
      apply h
      rw [← he, inv_mul_cancel_right]
    simp [h, h']

/-- For [product-group elements g and q](hyp:g,q), [left regular translation by g commutes
with right regular translation by q](goal). -/
-- @node: lamReg_commute_rhoReg
lemma lamReg_commute_rhoReg (g q : ProdGrp) : Commute (lamReg g) (rhoReg q) := by
  ext ξ x
  simp only [lamReg, rhoReg, mul_apply_eq_comp, lpReindex_apply,
    Equiv.coe_mulLeft, Equiv.coe_mulRight, mul_assoc]

/-- For [a bounded operator X on the scalar square-summable product-group space](hyp:X)
that [belongs to the bicommutant of the left regular representation](hyp:hX), and
[product-group elements x, y, and q](hyp:x,y,q), [the matrix entry of X at row x times q and
column y times q equals its entry at row x and column y](goal). -/
-- @node: scalar_entry_right_invariant
lemma scalar_entry_right_invariant (X : Ssp →L[ℂ] Ssp)
    (hX : X ∈ commutant (commutant (Set.range lamReg))) (x y q : ProdGrp) :
    X (prodBasis (y * q)) (x * q) = X (prodBasis y) x := by
  have hr : rhoReg q ∈ commutant (Set.range lamReg) := by
    rintro _ ⟨g, rfl⟩
    exact (lamReg_commute_rhoReg g q).eq
  have hc := hX (rhoReg q) hr
  have hs : rhoReg q (prodBasis (y * q)) = prodBasis y := by
    ext z
    simp only [rhoReg, lpReindex_apply, Equiv.coe_mulRight, prodBasis, lp.single_apply]
    by_cases h : y = z <;> simp [h]
  have he := congrArg (fun T : Ssp →L[ℂ] Ssp => T (prodBasis (y * q)) x) hc
  simp only [mul_apply_eq_comp, rhoReg, lpReindex_apply, Equiv.coe_mulRight] at he
  change X (prodBasis (y * q)) (x * q) = X (rhoReg q (prodBasis (y * q))) x at he
  rw [hs] at he
  exact he

/-- For [a bounded operator Y on the vector-valued product-group space](hyp:Y) and
[product-group elements q, x, and y](hyp:q,x,y), [the block at row x and column y of amplified
right translation by q composed with Y is the block of Y at row x times q and column y](goal). -/
-- @node: hspBlock_rhoAmp_mul
lemma hspBlock_rhoAmp_mul (Y : Hsp D →L[ℂ] Hsp D) (q x y : ProdGrp) :
    hspBlock (rhoAmp q * Y) x y = hspBlock Y (x * q) y := by
  ext v
  simp only [hspBlock_apply, mul_apply_eq_comp, rhoAmp, lpReindex_apply,
    Equiv.coe_mulRight]

/-- For [a bounded operator Y on the vector-valued product-group space](hyp:Y) and
[product-group elements q, x, and y](hyp:q,x,y), [the block at row x and column y of Y composed
with amplified right translation by q is the block of Y at row x and column y times the
inverse of q](goal). -/
-- @node: hspBlock_mul_rhoAmp
lemma hspBlock_mul_rhoAmp (Y : Hsp D →L[ℂ] Hsp D) (q x y : ProdGrp) :
    hspBlock (Y * rhoAmp q) x y = hspBlock Y x (y * q⁻¹) := by
  ext v
  simp only [hspBlock_apply, mul_apply_eq_comp, rhoAmp_single]

/-- For [a bounded operator Y on the vector-valued product-group space](hyp:Y), if
[every block is unchanged when its row and column indices are multiplied on the right by
the same group element](hyp:hY), then [Y belongs to the target algebra, the commutant of
amplified right translations](goal). -/
-- @node: mem_targetAlg_of_blocks_right_invariant
lemma mem_targetAlg_of_blocks_right_invariant (Y : Hsp D →L[ℂ] Hsp D)
    (hY : ∀ x y q, hspBlock Y (x * q) (y * q) = hspBlock Y x y) :
    Y ∈ targetAlg (D := D) := by
  rw [← SetLike.mem_coe, targetAlg_carrier]
  rintro _ ⟨q, rfl⟩
  apply hspBlock_ext
  intro x y
  rw [hspBlock_rhoAmp_mul, hspBlock_mul_rhoAmp]
  simpa only [inv_mul_cancel_right] using hY x (y * q⁻¹) q

/-- Let [X be a bounded operator on the scalar square-summable product-group space](hyp:X)
that [belongs to the bicommutant of the left regular representation](hyp:hX), let
[f assign a bounded operator on L to each product-group element](hyp:f), and let
[Y be a bounded operator on the vector-valued product-group space](hyp:Y).
If [each block of Y at row x and column y is the corresponding scalar entry of X times
f evaluated at x times the inverse of y](hyp:hY), then [Y belongs to the target algebra](goal). -/
-- @node: mem_targetAlg_of_reordered_blocks
lemma mem_targetAlg_of_reordered_blocks (X : Ssp →L[ℂ] Ssp)
    (hX : X ∈ commutant (commutant (Set.range lamReg)))
    (f : ProdGrp → Lsp D →L[ℂ] Lsp D) (Y : Hsp D →L[ℂ] Hsp D)
    (hY : ∀ x y, hspBlock Y x y = (X (prodBasis y) x) • f (x * y⁻¹)) :
    Y ∈ targetAlg (D := D) := by
  apply mem_targetAlg_of_blocks_right_invariant
  intro x y q
  rw [hY, hY, scalar_entry_right_invariant X hX]
  congr 2
  group

/-- Given [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), take [operators U and V on a finite-dimensional
Hilbert space](hyp:U,V) with [U unitary](hyp:hU) and [V unitary](hyp:hV), and
[a scalar-space operator X](hyp:X) that [belongs to the bicommutant of the left regular
representation](hyp:hX). If [a bounded operator Y on the vector-valued product-group space](hyp:Y)
has [each block equal to the corresponding entry of X times, in order, the first substituted
operator at the row's first coordinate, its adjoint at the column's first coordinate, the
second substituted operator at the row's second coordinate, and its adjoint at the column's
second coordinate](hyp:hY), then [Y belongs to the target algebra](goal). -/
-- @node: mem_targetAlg_of_matrixRep_blocks
lemma mem_targetAlg_of_matrixRep_blocks [FiniteDimensional ℂ D]
    (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U V : D →L[ℂ] D) (hU : U ∈ unitary _) (hV : V ∈ unitary _)
    (X : Ssp →L[ℂ] Ssp) (hX : X ∈ commutant (commutant (Set.range lamReg)))
    (Y : Hsp D →L[ℂ] Hsp D)
    (hY : ∀ x y, hspBlock Y x y = (X (prodBasis y) x) •
      (matrixRepA A U x.1 * star (matrixRepA A U y.1) *
        (matrixRepB A V x.2 * star (matrixRepB A V y.2)))) :
    Y ∈ targetAlg (D := D) := by
  apply mem_targetAlg_of_reordered_blocks X hX (prodMap A U V) Y
  intro x y
  rw [hY, reordered_block_product π A hπ U V hU hV]

/-- For [any product-group element g](hyp:g), [left regular translation by g belongs to
the bicommutant of the left regular representation](goal). -/
-- @node: lamReg_mem_bicommutant
lemma lamReg_mem_bicommutant (g : ProdGrp) :
    lamReg g ∈ commutant (commutant (Set.range lamReg)) :=
  Set.subset_centralizer_centralizer ⟨g, rfl⟩

/-- Let [f assign a bounded operator on L to each product-group element](hyp:f), let
[g be a product-group element](hyp:g), and let [Y be a bounded operator on the vector-valued
product-group space](hyp:Y). If [the block of Y at row x and column y is the corresponding
entry of left regular translation by g times f evaluated at x times the inverse of y](hyp:hY),
then [Y is amplified left translation by g composed with the operator applying f at g
to every coordinate](goal). -/
-- @node: eq_lamAmp_mul_of_reordered_blocks
lemma eq_lamAmp_mul_of_reordered_blocks
    (f : ProdGrp → Lsp D →L[ℂ] Lsp D) (g : ProdGrp)
    (Y : Hsp D →L[ℂ] Hsp D)
    (hY : ∀ x y, hspBlock Y x y = (lamReg g (prodBasis y) x) • f (x * y⁻¹)) :
    Y = lamAmp g * lp.mapCLM 2 (fun _ : ProdGrp => f g)
      (norm_nonneg _) (fun _ => le_rfl) := by
  apply hspBlock_ext
  intro x y
  rw [hY]
  apply ContinuousLinearMap.ext
  intro v
  rw [hspBlock_apply]
  simp only [smul_apply, mul_apply_eq_comp, lamAmp,
    lpReindex_apply, Equiv.coe_mulLeft, lamReg, prodBasis,
    lp.single_apply]
  by_cases h : y = g⁻¹ * x
  · have hg : x * y⁻¹ = g := by rw [h]; group
    rw [hg]
    simp [h]
  · simp [h]

/-- For [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), take [integer coefficient indices k and m](hyp:k,m),
[a product-group location y](hyp:y), and [a vector v in L](hyp:v). Then
[the adjoint of the diagonal coefficient operator sends the sequence supported at y with
value v to the sequence supported at y whose value is the adjoint of the product of the
first-factor coefficient k at the first coordinate of y and the second-factor coefficient m
at the second coordinate of y, applied to v](goal). -/
-- @node: nearCoeffDiag_star_single
lemma nearCoeffDiag_star_single (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (k m : ℤ) (y : ProdGrp) (v : Lsp D) :
    star (nearCoeffDiag π A hπ k m) (lp.single 2 y v) =
      lp.single 2 y (star (ampFst (D := D) (A k y.1) * ampSnd (D := D) (A m y.2)) v) := by
  unfold nearCoeffDiag
  rw [lpMap_star]
  ext x
  by_cases h : y = x <;> simp [lp.single_apply, h]

/-- For [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), [a bounded scalar-space operator X](hyp:X),
[four integer indices q, ordered as k, m, p, h](hyp:q), and [product-group row and column
locations x and y](hyp:x,y), [the corresponding block of the fourfold coefficient is the
scalar entry of X at x and y times the product of the first-factor coefficient k at the
first coordinate of x and the second-factor coefficient m at the second coordinate of x,
followed by the adjoint of the product of the first-factor coefficient h at the first
coordinate of y and the second-factor coefficient p at the second coordinate of y](goal). -/
-- @node: nearCoeffBlock_block
lemma nearCoeffBlock_block (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (X : Ssp →L[ℂ] Ssp)
    (q : ℤ × ℤ × ℤ × ℤ) (x y : ProdGrp) :
    hspBlock (nearCoeffBlock (D := D) π A hπ X q) x y =
      (X (prodBasis y) x) •
        ((ampFst (D := D) (A q.1 x.1) * ampSnd (D := D) (A q.2.1 x.2)) *
          star (ampFst (D := D) (A q.2.2.2 y.1) * ampSnd (D := D) (A q.2.2.1 y.2))) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [hspBlock_apply]
  simp only [nearCoeffBlock, mul_apply_eq_comp, nearCoeffDiag_star_single]
  change (ampFst (D := D) (A q.1 x.1) * ampSnd (D := D) (A q.2.1 x.2))
    (amplify X (lp.single 2 y
      (star (ampFst (D := D) (A q.2.2.2 y.1) * ampSnd (D := D) (A q.2.2.1 y.2)) v)) x) = _
  rw [(amplify_spec X).1, map_smul]
  rfl

end Papers.OaiNearInclusionsVon
