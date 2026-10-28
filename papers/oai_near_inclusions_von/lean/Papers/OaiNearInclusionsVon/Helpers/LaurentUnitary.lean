module

public import Papers.OaiNearInclusionsVon.Helpers.NearConstruction
public import Papers.OaiNearInclusionsVon.Helpers.UnitarySpectrum

/-! Laurent substitution on unitary eigenspaces and unitarity of the diagonal operator. -/

public section

namespace Papers.OaiNearInclusionsVon

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

/-- If [T sends v to a times v](hyp:hv), then [the n-th power of T sends v to
a to the n-th power times v](goal). -/
-- @node: operator_pow_apply_eigen
lemma operator_pow_apply_eigen (T : D →L[ℂ] D) (a : ℂ) (v : D)
    (hv : T v = a • v) (n : ℕ) : (T ^ n) v = a ^ n • v := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ', mul_apply_eq_comp, hn, map_smul, hv, smul_smul, pow_succ]

-- @node: unitaryIntPow_apply_eigen
/-- If [U is unitary](hyp:hU) and [v is an eigenvector of U with eigenvalue z on
the unit circle](hyp:hv), then [every integer power k of U sends v to z to the
k-th power times v](goal). -/
lemma unitaryIntPow_apply_eigen (U : D →L[ℂ] D) (hU : U ∈ unitary _)
    (z : Circle) (v : D) (hv : U v = (z : ℂ) • v) (k : ℤ) :
    unitaryIntPow U k v = (z : ℂ) ^ k • v := by
  cases k with
  | ofNat n => simpa [unitaryIntPow] using operator_pow_apply_eigen U _ v hv n
  | negSucc n =>
    have hstar := unitary_star_apply_eigen U hU z v hv
    have hz : star (z : ℂ) = (z : ℂ)⁻¹ :=
      (Circle.coe_inv_eq_conj z).symm.trans (Circle.coe_inv z)
    simpa [unitaryIntPow, zpow_negSucc, hz, inv_pow] using
      operator_pow_apply_eigen (star U) _ v hstar (n + 1)

/-- In a finite-dimensional coefficient space, if [U is unitary](hyp:hU) and
[S and T agree on every elementary tensor whose coefficient vector is an
eigenvector of U](hyp:h), then [S and T are equal](goal). -/
-- @node: lsp_ext_on_eigenvectors
lemma lsp_ext_on_eigenvectors [FiniteDimensional ℂ D]
    (U : D →L[ℂ] D) (hU : U ∈ unitary _) (S T : Lsp D →L[ℂ] Lsp D)
    (h : ∀ (z : Circle) (v : D), U v = (z : ℂ) • v → ∀ x y : TreeSpace,
      S (lpTensorRight (lpTensorRight v y) x) =
        T (lpTensorRight (lpTensorRight v y) x)) : S = T := by
  apply lp.ext_continuousLinearMap (by norm_num)
  intro i
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  apply unitary_ext_on_eigenvectors U hU
  intro z v hv
  simpa only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    treeBasis, lpTensorRight_single] using h z v hv (treeBasis i) (treeBasis j)

-- @node: ampD_tensorRight
/-- [Applying the amplification of Y to an elementary three-factor tensor
applies Y to its coefficient vector v and leaves both tree-space factors
unchanged](goal). -/
lemma ampD_tensorRight (Y : D →L[ℂ] D) (v : D) (x y : TreeSpace) :
    ampD Y (lpTensorRight (lpTensorRight v y) x) =
      lpTensorRight (lpTensorRight (Y v) y) x := by
  ext i j
  change Y (x i • (y j • v)) = x i • (y j • Y v)
  simp only [map_smul]

-- @node: ampSnd_tensorRight
/-- [Applying the second tree-space amplification of X to an elementary tensor
with factors x, y, and v replaces y by X applied to y and leaves x and v
unchanged](goal). -/
lemma ampSnd_tensorRight (X : TreeSpace →L[ℂ] TreeSpace) (v : D) (x y : TreeSpace) :
    ampSnd X (lpTensorRight (lpTensorRight v y) x) =
      lpTensorRight (lpTensorRight v (X y)) x := by
  ext i j
  change amplify X (x i • lpTensorRight v y) j = x i • lpTensorRight v (X y) j
  rw [map_smul, amplify_tensorRight]
  rfl

-- @node: ampSnd_star
/-- [The adjoint of the second tree-space amplification of X equals the second
tree-space amplification of the adjoint of X](goal). -/
lemma ampSnd_star (X : TreeSpace →L[ℂ] TreeSpace) :
    star (ampSnd (D := D) X) = ampSnd (star X) := by
  unfold ampSnd
  rw [lpMap_star]
  congr 1
  · funext i
    exact (amplify_star X).symm
  · simp only [norm_star]

-- @node: aTerm_tensorRight_eigen
/-- If [U is unitary](hyp:hU) and [v is an eigenvector of U with eigenvalue z on
the unit circle](hyp:hv), then [the k-th first-factor Laurent term at g acts on
an elementary tensor by applying the coefficient operator A at k and g to x,
scaling that result by z to the k-th power, and leaving y and v unchanged](goal). -/
lemma aTerm_tensorRight_eigen (A : LaurentData) (U : D →L[ℂ] D)
    (hU : U ∈ unitary _) (z : Circle) (v : D) (hv : U v = (z : ℂ) • v)
    (g : FreeGrp) (k : ℤ) (x y : TreeSpace) :
    aTerm A U k g (lpTensorRight (lpTensorRight v y) x) =
      lpTensorRight (lpTensorRight v y) (((z : ℂ) ^ k) • (A k g x)) := by
  rw [aTerm, mul_apply_eq_comp, ampD_tensorRight, unitaryIntPow_apply_eigen U hU z v hv]
  rw [ampFst, amplify_tensorRight]
  ext i j
  simp only [lpTensorRight_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  ring

-- @node: bTerm_tensorRight_eigen
/-- If [U is unitary](hyp:hU) and [v is an eigenvector of U with eigenvalue z on
the unit circle](hyp:hv), then [the k-th second-factor Laurent term at g acts on
an elementary tensor by applying the coefficient operator A at k and g to y,
scaling that result by z to the k-th power, and leaving x and v unchanged](goal). -/
lemma bTerm_tensorRight_eigen (A : LaurentData) (U : D →L[ℂ] D)
    (hU : U ∈ unitary _) (z : Circle) (v : D) (hv : U v = (z : ℂ) • v)
    (g : FreeGrp) (k : ℤ) (x y : TreeSpace) :
    bTerm A U k g (lpTensorRight (lpTensorRight v y) x) =
      lpTensorRight (lpTensorRight v (((z : ℂ) ^ k) • (A k g y))) x := by
  rw [bTerm, mul_apply_eq_comp, ampD_tensorRight, unitaryIntPow_apply_eigen U hU z v hv,
    ampSnd_tensorRight]
  ext i j
  simp only [lpTensorRight_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  ring

-- @node: aTerm_star_tensorRight_eigen
/-- If [U is unitary](hyp:hU) and [v is an eigenvector of U with eigenvalue z on
the unit circle](hyp:hv), then [the adjoint of the k-th first-factor Laurent term
at g applies the adjoint of the coefficient operator scaled by z to the k-th
power to x, leaving y and v unchanged](goal). -/
lemma aTerm_star_tensorRight_eigen (A : LaurentData) (U : D →L[ℂ] D)
    (hU : U ∈ unitary _) (z : Circle) (v : D) (hv : U v = (z : ℂ) • v)
    (g : FreeGrp) (k : ℤ) (x y : TreeSpace) :
    star (aTerm A U k g) (lpTensorRight (lpTensorRight v y) x) =
      lpTensorRight (lpTensorRight v y)
        (star (((z : ℂ) ^ k) • A k g) x) := by
  have he := unitary_star_apply_eigen (unitaryIntPow U k)
    (unitaryIntPow_mem_unitary U hU k) (z ^ k) v
    (unitaryIntPow_apply_eigen U hU z v hv k)
  change star (unitaryIntPow U k) v = star ((z : ℂ) ^ k) • v at he
  rw [aTerm, star_mul, ← ampD_star]
  change ampD (star (unitaryIntPow U k))
    (star (amplify (A k g)) (lpTensorRight (lpTensorRight v y) x)) = _
  rw [← amplify_star, amplify_tensorRight, ampD_tensorRight, he]
  ext i j
  simp only [lpTensorRight_apply, star_smul, smul_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, smul_smul]
  congr 1
  ring

-- @node: bTerm_star_tensorRight_eigen
/-- If [U is unitary](hyp:hU) and [v is an eigenvector of U with eigenvalue z on
the unit circle](hyp:hv), then [the adjoint of the k-th second-factor Laurent term
at g applies the adjoint of the coefficient operator scaled by z to the k-th
power to y, leaving x and v unchanged](goal). -/
lemma bTerm_star_tensorRight_eigen (A : LaurentData) (U : D →L[ℂ] D)
    (hU : U ∈ unitary _) (z : Circle) (v : D) (hv : U v = (z : ℂ) • v)
    (g : FreeGrp) (k : ℤ) (x y : TreeSpace) :
    star (bTerm A U k g) (lpTensorRight (lpTensorRight v y) x) =
      lpTensorRight (lpTensorRight v (star (((z : ℂ) ^ k) • A k g) y)) x := by
  have he := unitary_star_apply_eigen (unitaryIntPow U k)
    (unitaryIntPow_mem_unitary U hU k) (z ^ k) v
    (unitaryIntPow_apply_eigen U hU z v hv k)
  change star (unitaryIntPow U k) v = star ((z : ℂ) ^ k) • v at he
  rw [bTerm, star_mul, ← ampD_star, ampSnd_star, mul_apply_eq_comp,
    ampSnd_tensorRight, ampD_tensorRight, he]
  ext i j
  simp only [lpTensorRight_apply, star_smul, smul_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, smul_smul]
  congr 1
  ring

/-- If [π and A satisfy the circle-family assumptions](hyp:hπ), [U is
unitary](hyp:hU), and [v is an eigenvector of U with eigenvalue z](hyp:hv), then
[the first-factor matrix substitution at g acts on the elementary tensor by
applying the circle representation at z and g to x, leaving y and v unchanged](goal). -/
-- @node: matrixRepA_tensorRight_eigen
lemma matrixRepA_tensorRight_eigen (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (U : D →L[ℂ] D) (hU : U ∈ unitary _)
    (z : Circle) (v : D) (hv : U v = (z : ℂ) • v)
    (g : FreeGrp) (x y : TreeSpace) :
    matrixRepA A U g (lpTensorRight (lpTensorRight v y) x) =
      lpTensorRight (lpTensorRight v y) ((π z g : TreeSpace →L[ℂ] TreeSpace) x) := by
  have ha := ((matrixRepsAbsConv_of_circleFamily π A hπ U U hU hU) g).1.of_norm.hasSum
  have hs := (ContinuousLinearMap.apply ℂ (Lsp D)
    (lpTensorRight (lpTensorRight v y) x)).hasSum ha
  have hp := ((lpTensorRight (lpTensorRight v y)).comp
    (ContinuousLinearMap.apply ℂ TreeSpace x)).hasSum (hπ.1 z g)
  change HasSum (fun k => aTerm A U k g (lpTensorRight (lpTensorRight v y) x))
    (matrixRepA A U g (lpTensorRight (lpTensorRight v y) x)) at hs
  simp_rw [aTerm_tensorRight_eigen A U hU z v hv] at hs
  exact hs.unique hp

-- @node: matrixRepA_star_tensorRight_eigen
/-- If [π and A satisfy the circle-family assumptions](hyp:hπ), [U is
unitary](hyp:hU), and [v is an eigenvector of U with eigenvalue z](hyp:hv), then
[the adjoint of the first-factor matrix substitution at g applies the adjoint
of the circle representation at z and g to x, leaving y and v unchanged](goal). -/
lemma matrixRepA_star_tensorRight_eigen (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (U : D →L[ℂ] D) (hU : U ∈ unitary _)
    (z : Circle) (v : D) (hv : U v = (z : ℂ) • v)
    (g : FreeGrp) (x y : TreeSpace) :
    star (matrixRepA A U g) (lpTensorRight (lpTensorRight v y) x) =
      lpTensorRight (lpTensorRight v y) (star (π z g : TreeSpace →L[ℂ] TreeSpace) x) := by
  have ha := ((matrixRepsAbsConv_of_circleFamily π A hπ U U hU hU) g).1.of_norm.hasSum.star
  have hs := (ContinuousLinearMap.apply ℂ (Lsp D)
    (lpTensorRight (lpTensorRight v y) x)).hasSum ha
  have hp := ((lpTensorRight (lpTensorRight v y)).comp
    (ContinuousLinearMap.apply ℂ TreeSpace x)).hasSum (hπ.1 z g).star
  change HasSum (fun k => star (aTerm A U k g) (lpTensorRight (lpTensorRight v y) x))
    (star (matrixRepA A U g) (lpTensorRight (lpTensorRight v y) x)) at hs
  simp_rw [aTerm_star_tensorRight_eigen A U hU z v hv] at hs
  exact hs.unique hp

-- @node: matrixRepB_tensorRight_eigen
/-- If [π and A satisfy the circle-family assumptions](hyp:hπ), [U is
unitary](hyp:hU), and [v is an eigenvector of U with eigenvalue z](hyp:hv), then
[the second-factor matrix substitution at g acts on the elementary tensor by
applying the circle representation at z and g to y, leaving x and v unchanged](goal). -/
lemma matrixRepB_tensorRight_eigen (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (U : D →L[ℂ] D) (hU : U ∈ unitary _)
    (z : Circle) (v : D) (hv : U v = (z : ℂ) • v)
    (g : FreeGrp) (x y : TreeSpace) :
    matrixRepB A U g (lpTensorRight (lpTensorRight v y) x) =
      lpTensorRight (lpTensorRight v ((π z g : TreeSpace →L[ℂ] TreeSpace) y)) x := by
  apply lp.ext
  funext i
  have ha := ((matrixRepsAbsConv_of_circleFamily π A hπ U U hU hU) g).2.of_norm.hasSum
  have hs := ((lp.evalCLM ℂ (fun _ : FreeGrp => lp (fun _ : FreeGrp => D) 2) 2 i).comp
    (ContinuousLinearMap.apply ℂ (Lsp D) (lpTensorRight (lpTensorRight v y) x))).hasSum ha
  have hp := (((lpTensorRight v).comp (ContinuousLinearMap.apply ℂ TreeSpace y)).hasSum
    (hπ.1 z g)).const_smul (x i)
  change HasSum (fun k => bTerm A U k g (lpTensorRight (lpTensorRight v y) x) i)
    (matrixRepB A U g (lpTensorRight (lpTensorRight v y) x) i) at hs
  simp_rw [bTerm_tensorRight_eigen A U hU z v hv] at hs
  exact hs.unique hp

-- @node: matrixRepB_star_tensorRight_eigen
/-- If [π and A satisfy the circle-family assumptions](hyp:hπ), [U is
unitary](hyp:hU), and [v is an eigenvector of U with eigenvalue z](hyp:hv), then
[the adjoint of the second-factor matrix substitution at g applies the adjoint
of the circle representation at z and g to y, leaving x and v unchanged](goal). -/
lemma matrixRepB_star_tensorRight_eigen (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (U : D →L[ℂ] D) (hU : U ∈ unitary _)
    (z : Circle) (v : D) (hv : U v = (z : ℂ) • v)
    (g : FreeGrp) (x y : TreeSpace) :
    star (matrixRepB A U g) (lpTensorRight (lpTensorRight v y) x) =
      lpTensorRight (lpTensorRight v (star (π z g : TreeSpace →L[ℂ] TreeSpace) y)) x := by
  apply lp.ext
  funext i
  have ha := ((matrixRepsAbsConv_of_circleFamily π A hπ U U hU hU) g).2.of_norm.hasSum.star
  have hs := ((lp.evalCLM ℂ (fun _ : FreeGrp => lp (fun _ : FreeGrp => D) 2) 2 i).comp
    (ContinuousLinearMap.apply ℂ (Lsp D) (lpTensorRight (lpTensorRight v y) x))).hasSum ha
  have hp := (((lpTensorRight v).comp (ContinuousLinearMap.apply ℂ TreeSpace y)).hasSum
    (hπ.1 z g).star).const_smul (x i)
  change HasSum (fun k => star (bTerm A U k g) (lpTensorRight (lpTensorRight v y) x) i)
    (star (matrixRepB A U g) (lpTensorRight (lpTensorRight v y) x) i) at hs
  simp_rw [bTerm_star_tensorRight_eigen A U hU z v hv] at hs
  exact hs.unique hp

-- @node: matrixRepA_mem_unitary
/-- On a finite-dimensional coefficient space, if [π and A satisfy the
circle-family assumptions](hyp:hπ) and [U is unitary](hyp:hU), then [the
first-factor matrix substitution at every group element g is unitary](goal). -/
lemma matrixRepA_mem_unitary [FiniteDimensional ℂ D]
    (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U : D →L[ℂ] D) (hU : U ∈ unitary _) (g : FreeGrp) :
    matrixRepA A U g ∈ unitary (Lsp D →L[ℂ] Lsp D) := by
  apply Unitary.mem_iff.mpr
  constructor
  · apply lsp_ext_on_eigenvectors U hU
    intro z v hv x y
    rw [mul_apply_eq_comp, matrixRepA_tensorRight_eigen π A hπ U hU z v hv,
      matrixRepA_star_tensorRight_eigen π A hπ U hU z v hv]
    change lpTensorRight (lpTensorRight v y)
      ((star (π z g : TreeSpace →L[ℂ] TreeSpace) * (π z g : TreeSpace →L[ℂ] TreeSpace)) x) = _
    rw [Unitary.star_mul_self_of_mem (π z g).property, one_apply_eq_self, one_apply_eq_self]
  · apply lsp_ext_on_eigenvectors U hU
    intro z v hv x y
    rw [mul_apply_eq_comp, matrixRepA_star_tensorRight_eigen π A hπ U hU z v hv,
      matrixRepA_tensorRight_eigen π A hπ U hU z v hv]
    change lpTensorRight (lpTensorRight v y)
      (((π z g : TreeSpace →L[ℂ] TreeSpace) * star (π z g : TreeSpace →L[ℂ] TreeSpace)) x) = _
    rw [Unitary.mul_star_self_of_mem (π z g).property, one_apply_eq_self, one_apply_eq_self]

-- @node: matrixRepB_mem_unitary
/-- On a finite-dimensional coefficient space, if [π and A satisfy the
circle-family assumptions](hyp:hπ) and [U is unitary](hyp:hU), then [the
second-factor matrix substitution at every group element g is unitary](goal). -/
lemma matrixRepB_mem_unitary [FiniteDimensional ℂ D]
    (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (U : D →L[ℂ] D) (hU : U ∈ unitary _) (g : FreeGrp) :
    matrixRepB A U g ∈ unitary (Lsp D →L[ℂ] Lsp D) := by
  apply Unitary.mem_iff.mpr
  constructor
  · apply lsp_ext_on_eigenvectors U hU
    intro z v hv x y
    rw [mul_apply_eq_comp, matrixRepB_tensorRight_eigen π A hπ U hU z v hv,
      matrixRepB_star_tensorRight_eigen π A hπ U hU z v hv]
    change lpTensorRight (lpTensorRight v
      ((star (π z g : TreeSpace →L[ℂ] TreeSpace) * (π z g : TreeSpace →L[ℂ] TreeSpace)) y)) x = _
    rw [Unitary.star_mul_self_of_mem (π z g).property, one_apply_eq_self, one_apply_eq_self]
  · apply lsp_ext_on_eigenvectors U hU
    intro z v hv x y
    rw [mul_apply_eq_comp, matrixRepB_star_tensorRight_eigen π A hπ U hU z v hv,
      matrixRepB_tensorRight_eigen π A hπ U hU z v hv]
    change lpTensorRight (lpTensorRight v
      (((π z g : TreeSpace →L[ℂ] TreeSpace) * star (π z g : TreeSpace →L[ℂ] TreeSpace)) y)) x = _
    rw [Unitary.mul_star_self_of_mem (π z g).property, one_apply_eq_self, one_apply_eq_self]

-- @node: diagUnitary_mem_unitary
/-- If [π and A satisfy the circle-family assumptions](hyp:hπ), [U and V are
unitary operators on a nonzero finite-dimensional coefficient space](hyp:hUV),
and [every product-map operator has norm at most the square of S₀](hyp:hb), then
[the diagonal operator formed from these product maps is unitary](goal). -/
lemma diagUnitary_mem_unitary (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (U V : D →L[ℂ] D) (hUV : NearUnitaryPair U V)
    (hb : ∀ x : ProdGrp, ‖prodMap A U V x‖ ≤ S0 ^ 2) :
    diagUnitary A U V hb ∈ unitary (Hsp D →L[ℂ] Hsp D) := by
  suffices hmatrix :
      (∀ g, matrixRepA A U g ∈ unitary (Lsp D →L[ℂ] Lsp D)) ∧
      (∀ g, matrixRepB A V g ∈ unitary (Lsp D →L[ℂ] Lsp D)) by
    exact lpMap_mem_unitary _ (sq_nonneg S0) hb
      (fun x => (unitary _).mul_mem (hmatrix.1 x.1) (hmatrix.2 x.2))
  letI : FiniteDimensional ℂ D := hUV.2.1
  exact ⟨matrixRepA_mem_unitary π A hπ U hUV.2.2.1,
    matrixRepB_mem_unitary π A hπ V hUV.2.2.2⟩

end Papers.OaiNearInclusionsVon
