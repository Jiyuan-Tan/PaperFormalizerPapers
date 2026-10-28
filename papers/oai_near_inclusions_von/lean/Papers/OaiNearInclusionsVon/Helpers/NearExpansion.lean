module

public import Papers.OaiNearInclusionsVon.Helpers.NearBlocks
public import Papers.OaiNearInclusionsVon.Helpers.SourceCarrier

/-! Blockwise assembly of the absolutely convergent Fourier expansions. -/

@[expose] public section

open scoped TensorProduct

namespace Papers.OaiNearInclusionsVon

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

-- @node: hspBlockCLM
/-- For [a Hilbert space D](hyp:D), [a row group pair x](hyp:x), and [a column
group pair y](hyp:y), the [continuous linear block-extraction map](goal) sends
an operator on the full sequence space to its operator-valued entry at row x
and column y. -/
noncomputable def hspBlockCLM (x y : ProdGrp) :
    (Hsp D →L[ℂ] Hsp D) →L[ℂ] (Lsp D →L[ℂ] Lsp D) :=
  (ContinuousLinearMap.compL ℂ (Lsp D) (Hsp D) (Lsp D)).flip
    (lp.singleContinuousLinearMap ℂ (fun _ : ProdGrp => Lsp D) 2 y) ∘L
  ContinuousLinearMap.compL ℂ (Hsp D) (Hsp D) (Lsp D)
    (lp.evalCLM ℂ (fun _ : ProdGrp => Lsp D) 2 x)

-- @node: hspBlockCLM_apply
/-- [Applying the continuous linear block-extraction map at row x and column y
to T gives the corresponding operator-valued block of T](goal). -/
lemma hspBlockCLM_apply (x y : ProdGrp) (T : Hsp D →L[ℂ] Hsp D) :
    hspBlockCLM x y T = hspBlock T x y := rfl

-- @node: hspBlock_tsum
/-- If [the operator family F is summable](hyp:hF), then [the block at row x and
column y of its sum equals the sum of its blocks at that row and column](goal). -/
lemma hspBlock_tsum {ι : Type*} (F : ι → (Hsp D →L[ℂ] Hsp D))
    (hF : Summable F) (x y : ProdGrp) :
    hspBlock (∑' i, F i) x y = ∑' i, hspBlock (F i) x y :=
  (hspBlockCLM (D := D) x y).map_tsum hF

-- @node: near_unitaryIntPow_neg
/-- If [U is unitary](hyp:hU), then [its integer power with exponent minus k is
the adjoint of its power with exponent k](goal). -/
lemma near_unitaryIntPow_neg (U : D →L[ℂ] D) (hU : U ∈ unitary _) (k : ℤ) :
    unitaryIntPow U (-k) = star (unitaryIntPow U k) := by
  simp only [near_unitaryIntPow_eq_zpow U hU, zpow_neg, ← Unitary.star_eq_inv,
    Unitary.coe_star]

-- @node: ampFst_commute_ampSnd
/-- [An operator X acting on the first tree factor commutes with an operator Y
acting on the second tree factor](goal). -/
lemma ampFst_commute_ampSnd (X Y : TreeSpace →L[ℂ] TreeSpace) :
    Commute (ampFst (D := D) X) (ampSnd (D := D) Y) :=
  amplify_commute_lpMap X (amplify (E := D) Y)

-- @node: hspBlock_mul_nearMatrixAmp
/-- [The block at row x and column y of T multiplied by the pointwise
amplification of Y equals the corresponding block of T followed by Y acting
on the D factor](goal). -/
lemma hspBlock_mul_nearMatrixAmp (T : Hsp D →L[ℂ] Hsp D)
    (Y : D →L[ℂ] D) (x y : ProdGrp) :
    hspBlock (T * nearMatrixAmp Y) x y = hspBlock T x y * ampD Y := by
  have hs (v : Lsp D) : nearMatrixAmp Y (lp.single 2 y v) =
      lp.single 2 y (ampD Y v) := by
    ext z
    by_cases h : y = z <;> simp [nearMatrixAmp, lp.single_apply, h]
  ext v
  simp only [hspBlock_apply, mul_apply_eq_comp, hs]

-- @node: near_collect_factors
/-- If [u commutes with b](hyp:h), then [the product of a followed by u and b
followed by v equals a followed by b and then u followed by v](goal). -/
lemma near_collect_factors {R : Type*} [Semigroup R] (a b u v : R)
    (h : Commute u b) : (a * u) * (b * v) = (a * b) * (u * v) := by
  simp only [mul_assoc]
  rw [← mul_assoc u b, h.eq, mul_assoc]

-- @node: near_ampFst_star
/-- [Taking the adjoint of X acting on the first tree factor gives the adjoint
of X acting on that same factor](goal). -/
lemma near_ampFst_star (X : TreeSpace →L[ℂ] TreeSpace) :
    star (ampFst (D := D) X) = ampFst (star X) := (amplify_star X).symm

-- @node: near_aTerm_star
/-- For [an integer Fourier index h](hyp:h), if [U is unitary](hyp:hU), then
[the adjoint of the first-factor Laurent term at h and group element g is the
adjoint coefficient of A at h and g acting on the first tree factor, followed
by U to power minus h acting on D](goal). -/
lemma near_aTerm_star (A : LaurentData) (U : D →L[ℂ] D)
    (hU : U ∈ unitary _) (h : ℤ) (g : FreeGrp) :
    star (aTerm A U h g) =
      ampFst (star (A h g)) * ampD (unitaryIntPow U (-h)) := by
  simp only [aTerm, star_mul, ← ampD_star, near_ampFst_star,
    ← near_unitaryIntPow_neg U hU]
  exact (ampFst_commute_ampD (D := D) _ _).symm.eq

-- @node: near_bTerm_star
/-- If [V is unitary](hyp:hV), then [the adjoint of the second-factor Laurent
term at p and group element g is the adjoint coefficient of A at p and g acting
on the second tree factor, followed by V to power minus p acting on D](goal). -/
lemma near_bTerm_star (A : LaurentData) (V : D →L[ℂ] D)
    (hV : V ∈ unitary _) (p : ℤ) (g : FreeGrp) :
    star (bTerm A V p g) =
      ampSnd (star (A p g)) * ampD (unitaryIntPow V (-p)) := by
  simp only [bTerm, star_mul, ← ampD_star, ampSnd_star, ← near_unitaryIntPow_neg V hV]
  exact (ampSnd_commute_ampD (D := D) _ _).symm.eq

-- @node: nearZTerm_block
/-- If [A is a circle family for π](hyp:hπ), [U is unitary](hyp:hU), and
[V is unitary](hyp:hV), then [the block at row x and column y of the original
expansion term with indices k, m, p, j equals the scalar matrix entry of X at
x and y times the ordered product of the first-factor term at k and x's first
group element, the second-factor term at m and x's second group element, the
adjoint second-factor term at p and y's second group element, and the adjoint
first-factor term at j and y's first group element](goal). -/
lemma nearZTerm_block (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (X : Ssp →L[ℂ] Ssp) (U V : D →L[ℂ] D)
    (hU : U ∈ unitary _) (hV : V ∈ unitary _)
    (q : ℤ × ℤ × ℤ × ℤ) (x y : ProdGrp) :
    hspBlock (nearZTerm (nearCoeffBlock π A hπ X) U V q) x y =
      (X (prodBasis y) x) •
        (aTerm A U q.1 x.1 * bTerm A V q.2.1 x.2 *
          star (bTerm A V q.2.2.1 y.2) * star (aTerm A U q.2.2.2 y.1)) := by
  rw [nearZTerm, hspBlock_mul_nearMatrixAmp, nearCoeffBlock_block, smul_mul_assoc]
  congr 1
  symm
  rw [near_aTerm_star A U hU, near_bTerm_star A V hV]
  unfold aTerm bTerm
  rw [near_collect_factors _ _ _ _ (ampSnd_commute_ampD (D := D) _ _).symm]
  rw [← ampD_mul]
  rw [near_collect_factors _ _ _ _ (ampSnd_commute_ampD (D := D) _ _).symm]
  rw [← ampD_mul]
  rw [near_collect_factors _ _ _ _ (ampFst_commute_ampD (D := D) _ _).symm]
  rw [← ampD_mul]
  simp only [star_mul, near_ampFst_star, ampSnd_star]
  rw [sub_eq_add_neg, near_unitaryIntPow_add V hV]
  simp only [mul_assoc]

-- @node: nearYTerm_block
/-- If [A is a circle family for π](hyp:hπ), [U is unitary](hyp:hU), and
[V is unitary](hyp:hV), then [the block at row x and column y of the reordered
expansion term with indices k, m, p, j equals the scalar matrix entry of X at
x and y times the first-factor term at k and x's first group element and the
adjoint first-factor term at j and y's first group element, followed by the
second-factor term at m and x's second group element and the adjoint
second-factor term at p and y's second group element](goal). -/
lemma nearYTerm_block (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (X : Ssp →L[ℂ] Ssp) (U V : D →L[ℂ] D)
    (hU : U ∈ unitary _) (hV : V ∈ unitary _)
    (q : ℤ × ℤ × ℤ × ℤ) (x y : ProdGrp) :
    hspBlock (nearYTerm (nearCoeffBlock π A hπ X) U V q) x y =
      (X (prodBasis y) x) •
        ((aTerm A U q.1 x.1 * star (aTerm A U q.2.2.2 y.1)) *
          (bTerm A V q.2.1 x.2 * star (bTerm A V q.2.2.1 y.2))) := by
  rw [nearYTerm, hspBlock_mul_nearMatrixAmp, nearCoeffBlock_block, smul_mul_assoc]
  congr 1
  symm
  rw [near_aTerm_star A U hU, near_bTerm_star A V hV]
  unfold aTerm bTerm
  rw [near_collect_factors _ _ _ _ (ampFst_commute_ampD (D := D) _ _).symm]
  rw [near_collect_factors _ _ _ _ (ampSnd_commute_ampD (D := D) _ _).symm]
  rw [← ampD_mul, ← ampD_mul]
  rw [near_collect_factors _ _ _ _
    ((ampSnd_commute_ampD (D := D) _ _).mul_left
      (ampSnd_commute_ampD (D := D) _ _)).symm]
  rw [← ampD_mul]
  simp only [star_mul, near_ampFst_star, ampSnd_star]
  simp only [sub_eq_add_neg, near_unitaryIntPow_add U hU, near_unitaryIntPow_add V hV]
  congr 1
  have hc := (ampFst_commute_ampSnd (D := D) (star (A q.2.2.2 y.1)) (A q.2.1 x.2)).mul_right
    (ampFst_commute_ampSnd (D := D) (star (A q.2.2.2 y.1)) (star (A q.2.2.1 y.2)))
  simpa only [mul_assoc] using congrArg (fun T => ampFst (D := D) (A q.1 x.1) * T) hc.eq

-- @node: near_fourfold_operator_product
/-- For [an integer-indexed family h in a complete normed ring](hyp:h), if
[the norms of the terms of f are summable](hyp:hf),
[those of g are summable](hyp:hg), [those of h are summable](hyp:hh), and
[those of l are summable](hyp:hl), then [the product of their four sums in the
order f, g, h, l equals the sum over all integer quadruples k, m, p, j of the
products of the corresponding terms in that order](goal). -/
lemma near_fourfold_operator_product {R : Type*} [NormedRing R] [CompleteSpace R]
    (f g h l : ℤ → R)
    (hf : Summable (fun k => ‖f k‖)) (hg : Summable (fun k => ‖g k‖))
    (hh : Summable (fun k => ‖h k‖)) (hl : Summable (fun k => ‖l k‖)) :
    (∑' k, f k) * ((∑' m, g m) * ((∑' p, h p) * ∑' j, l j)) =
      ∑' q : ℤ × ℤ × ℤ × ℤ, f q.1 * (g q.2.1 * (h q.2.2.1 * l q.2.2.2)) := by
  rw [tsum_mul_tsum_of_summable_norm hh hl,
    tsum_mul_tsum_of_summable_norm hg (hh.mul_norm hl),
    tsum_mul_tsum_of_summable_norm hf (hg.mul_norm (hh.mul_norm hl))]

-- @node: nearZ_expansion
/-- If [A is a circle family for π](hyp:hπ), [U is unitary](hyp:hU),
[V is unitary](hyp:hV), and [the norm of the product representation at every
group pair is at most S₀ squared](hyp:hb), then [the diagonal operator times
the amplification of X times the adjoint diagonal operator equals the sum of
the original four-index expansion terms](goal). -/
lemma nearZ_expansion (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (X : Ssp →L[ℂ] Ssp) (U V : D →L[ℂ] D)
    (hU : U ∈ unitary _) (hV : V ∈ unitary _)
    (hb : ∀ x : ProdGrp, ‖prodMap A U V x‖ ≤ S0 ^ 2) :
    diagUnitary A U V hb * amplify X * star (diagUnitary A U V hb) =
      ∑' q, nearZTerm (nearCoeffBlock π A hπ X) U V q := by
  have hconv := matrixRepsAbsConv_of_circleFamily π A hπ U V hU hV
  have hz := (near_laurent_series_absConv (nearCoeffBlock π A hπ X) U V hU hV
    ‖X‖ (nearCoeffBlock_norm_le π A hπ X)).1
  apply hspBlock_ext
  intro x y
  rw [diagUnitary_conjugate_block, hspBlock_tsum _ hz.of_norm]
  simp_rw [nearZTerm_block π A hπ X U V hU hV, mul_assoc]
  have ha := (hconv x.1).1
  have hb' := (hconv x.2).2
  have hc : Summable (fun p => ‖star (bTerm A V p y.2)‖) := by
    simpa only [norm_star] using (hconv y.2).2
  have hd : Summable (fun j => ‖star (aTerm A U j y.1)‖) := by
    simpa only [norm_star] using (hconv y.1).1
  rw [(ha.mul_norm (hb'.mul_norm (hc.mul_norm hd))).of_norm.tsum_const_smul]
  rw [← near_fourfold_operator_product _ _ _ _ ha hb' hc hd]
  simp only [prodMap, matrixRepA, matrixRepB, star_mul, ← tsum_star, mul_assoc]

-- @node: near_fourfold_reordered_product
/-- For [an integer-indexed family h in a complete normed ring](hyp:h), if
[the norms of the terms of f are summable](hyp:hf),
[those of g are summable](hyp:hg), [those of h are summable](hyp:hh), and
[those of l are summable](hyp:hl), then [the product of the sums in the order
f, l, g, h equals the sum over integer quadruples k, m, p, j of the k-th term
of f times the j-th term of l times the m-th term of g times the p-th term
of h](goal). -/
lemma near_fourfold_reordered_product {R : Type*} [NormedRing R] [CompleteSpace R]
    (f g h l : ℤ → R)
    (hf : Summable (fun k => ‖f k‖)) (hg : Summable (fun k => ‖g k‖))
    (hh : Summable (fun k => ‖h k‖)) (hl : Summable (fun k => ‖l k‖)) :
    (∑' k, f k) * (∑' j, l j) * ((∑' m, g m) * ∑' p, h p) =
      ∑' q : ℤ × ℤ × ℤ × ℤ, (f q.1 * l q.2.2.2) * (g q.2.1 * h q.2.2.1) := by
  let e : (ℤ × ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ × ℤ) :=
    { toFun := fun q => (q.1, q.2.2.2, q.2.1, q.2.2.1)
      invFun := fun q => (q.1, q.2.2.1, q.2.2.2, q.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [mul_assoc, near_fourfold_operator_product f l g h hf hl hg hh]
  have he := (e.tsum_eq (fun q => f q.1 * (l q.2.1 * (g q.2.2.1 * h q.2.2.2)))).symm
  change (∑' q : ℤ × ℤ × ℤ × ℤ, f q.1 * (l q.2.1 * (g q.2.2.1 * h q.2.2.2))) =
    ∑' q : ℤ × ℤ × ℤ × ℤ, f q.1 * (l q.2.2.2 * (g q.2.1 * h q.2.2.1)) at he
  simpa only [mul_assoc] using he

-- @node: nearY_expansion_blocks
/-- If [A is a circle family for π](hyp:hπ), [U is unitary](hyp:hU), and
[V is unitary](hyp:hV), then [the block at row x and column y of the reordered
series equals the scalar matrix entry of X at x and y times the first matrix
representation at x's first group element and its adjoint at y's first group
element, followed by the second matrix representation at x's second group
element and its adjoint at y's second group element](goal). -/
lemma nearY_expansion_blocks (π : CircleRep) (A : LaurentData) (hπ : IsCircleFamily π A)
    (X : Ssp →L[ℂ] Ssp) (U V : D →L[ℂ] D)
    (hU : U ∈ unitary _) (hV : V ∈ unitary _) (x y : ProdGrp) :
    hspBlock (∑' q, nearYTerm (nearCoeffBlock π A hπ X) U V q) x y =
      (X (prodBasis y) x) •
        (matrixRepA A U x.1 * star (matrixRepA A U y.1) *
          (matrixRepB A V x.2 * star (matrixRepB A V y.2))) := by
  have hconv := matrixRepsAbsConv_of_circleFamily π A hπ U V hU hV
  have hy := (near_laurent_series_absConv (nearCoeffBlock π A hπ X) U V hU hV
    ‖X‖ (nearCoeffBlock_norm_le π A hπ X)).2
  rw [hspBlock_tsum _ hy.of_norm]
  simp_rw [nearYTerm_block π A hπ X U V hU hV]
  have ha := (hconv x.1).1
  have hb := (hconv x.2).2
  have hc : Summable (fun p => ‖star (bTerm A V p y.2)‖) := by
    simpa only [norm_star] using (hconv y.2).2
  have hd : Summable (fun j => ‖star (aTerm A U j y.1)‖) := by
    simpa only [norm_star] using (hconv y.1).1
  have hprod : Summable (fun q : ℤ × ℤ × ℤ × ℤ =>
      aTerm A U q.1 x.1 * star (aTerm A U q.2.2.2 y.1) *
        (bTerm A V q.2.1 x.2 * star (bTerm A V q.2.2.1 y.2))) := by
    have hs := ha.mul_of_nonneg (hb.mul_of_nonneg (hc.mul_of_nonneg hd
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
      (fun _ => norm_nonneg _) (fun _ => by positivity))
      (fun _ => norm_nonneg _) (fun _ => by positivity)
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
    intro q
    calc
      _ ≤ (‖aTerm A U q.1 x.1‖ * ‖star (aTerm A U q.2.2.2 y.1)‖) *
          (‖bTerm A V q.2.1 x.2‖ * ‖star (bTerm A V q.2.2.1 y.2)‖) :=
        (norm_mul_le _ _).trans
          (mul_le_mul (norm_mul_le _ _) (norm_mul_le _ _) (norm_nonneg _) (by positivity))
      _ = _ := by ring
  rw [hprod.tsum_const_smul]
  rw [← near_fourfold_reordered_product _ _ _ _ ha hb hc hd]
  simp only [matrixRepA, matrixRepB, ← tsum_star]

-- @node: lpTensorRight_norm
/-- For [a square-summable scalar sequence x](hyp:x), [the norm of its elementary
tensor with a vector v equals the norm of x times the norm of v](goal). -/
lemma lpTensorRight_norm {I E : Type*} [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (v : E) (x : lp (fun _ : I => ℂ) 2) :
    ‖lpTensorRight v x‖ = ‖x‖ * ‖v‖ := by
  have he : lpTensorRight v x = lpTensorIsometry (x ⊗ₜ[ℂ] v) := rfl
  rw [he, LinearIsometry.norm_map, TensorProduct.norm_tmul]

-- @node: amplify_norm_eq
/-- For [an operator X on the square-summable scalar sequences](hyp:X),
[amplifying X by a nonzero Hilbert space preserves its operator norm](goal). -/
lemma amplify_norm_eq {I E : Type*} [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    (X : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    ‖amplify (E := E) X‖ = ‖X‖ := by
  apply le_antisymm (amplify_spec X).2
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have h := (amplify (E := E) X).le_opNorm (lpTensorRight v x)
  rw [amplify_tensorRight, lpTensorRight_norm, lpTensorRight_norm] at h
  apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv)).mp
  simpa only [mul_assoc] using h

-- @node: near_group_reordering_bound
/-- If [A is a circle family for π](hyp:hπ), [U and V are unitary operators on
a nonzero finite-dimensional Hilbert space](hyp:hUV), and [the norm of the
product representation at every group pair is at most S₀ squared](hyp:hb), then
[the norm of the difference between the diagonal conjugate of left translation
by g and left translation by g followed by the constant product representation
at g is at most nearC times the norm of UV minus VU](goal). -/
lemma near_group_reordering_bound (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (U V : D →L[ℂ] D) (hUV : NearUnitaryPair U V)
    (hb : ∀ x : ProdGrp, ‖prodMap A U V x‖ ≤ S0 ^ 2) (g : ProdGrp) :
    ‖diagUnitary A U V hb * lamAmp g * star (diagUnitary A U V hb) -
      lamAmp g * lp.mapCLM 2 (fun _ : ProdGrp => prodMap A U V g)
        (norm_nonneg _) (fun _ => le_rfl)‖ ≤ nearC * ‖U * V - V * U‖ := by
  let : FiniteDimensional ℂ D := hUV.2.1
  have hz : diagUnitary A U V hb * lamAmp g * star (diagUnitary A U V hb) =
      ∑' q, nearZTerm (nearCoeffBlock π A hπ (lamReg g)) U V q := by
    rw [lamAmp_eq_amplify]
    exact nearZ_expansion π A hπ (lamReg g) U V hUV.2.2.1 hUV.2.2.2 hb
  have hy := eq_lamAmp_mul_of_reordered_blocks (prodMap A U V) g
    (∑' q, nearYTerm (nearCoeffBlock π A hπ (lamReg g)) U V q)
    (fun x y => (nearY_expansion_blocks π A hπ (lamReg g) U V hUV.2.2.1 hUV.2.2.2 x y).trans
      (by rw [reordered_block_product π A hπ U V hUV.2.2.1 hUV.2.2.2]))
  have hlam : ‖lamReg g‖ ≤ 1 := by
    unfold lamReg
    rw [lpReindex_eq_isometry]
    exact (lpReindexIsometry (E := ℂ) (Equiv.mulLeft g⁻¹)).norm_toContinuousLinearMap_le
  have hB (q) : ‖nearCoeffBlock (D := D) π A hπ (lamReg g) q‖ ≤ nearCoeffWeight q * 1 :=
    (nearCoeffBlock_norm_le π A hπ (lamReg g) q).trans
      (mul_le_mul_of_nonneg_left hlam (nearCoeffWeight_nonneg q))
  rw [hz, ← hy]
  simpa only [mul_one] using near_laurent_series_reordering_le
    (nearCoeffBlock π A hπ (lamReg g)) U V hUV.2.2.1 hUV.2.2.2 1 hB

end Papers.OaiNearInclusionsVon
