module

public import Papers.OaiNearInclusionsVon.Helpers.NearSummability

/-! Absolute operator series and the four-factor Laurent reordering estimate. -/

@[expose] public section

namespace Papers.OaiNearInclusionsVon

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

-- @node: nearMatrixAmp
/-- For [a Hilbert space D](hyp:D) and [an operator Y on D](hyp:Y), the [matrix amplification of Y](goal)
acts by Y on the D coordinate at every sequence index. -/
noncomputable def nearMatrixAmp (Y : D →L[ℂ] D) : Hsp D →L[ℂ] Hsp D :=
  lp.mapCLM 2 (fun _ : ProdGrp => ampD Y) (norm_nonneg Y)
    (fun _ => ampD_norm_le Y)

-- @node: nearMatrixAmp_norm_le
/-- [The operator norm of the pointwise matrix amplification of Y is at most the
operator norm of Y](goal). -/
lemma nearMatrixAmp_norm_le (Y : D →L[ℂ] D) : ‖nearMatrixAmp Y‖ ≤ ‖Y‖ := by
  exact lp.norm_mapCLM_le 2 _ (norm_nonneg Y) _

-- @node: nearMatrixAmp_sub
/-- [Pointwise matrix amplification preserves the difference of two operators Y
and Z](goal). -/
lemma nearMatrixAmp_sub (Y Z : D →L[ℂ] D) :
    nearMatrixAmp (Y - Z) = nearMatrixAmp Y - nearMatrixAmp Z := by
  ext ξ x y z
  rfl

-- @node: nearCoeffWeight
/-- For [a quadruple q of integer Fourier indices](hyp:q), the [fourfold coefficient
weight](goal) is the product of the scalar coefficient weights at its four indices. -/
noncomputable def nearCoeffWeight (q : ℤ × ℤ × ℤ × ℤ) : ℝ :=
  cWeight q.1 * cWeight q.2.1 * cWeight q.2.2.1 * cWeight q.2.2.2

-- @node: nearCoeffWeight_nonneg
/-- [The fourfold coefficient weight at every integer quadruple q is nonnegative](goal). -/
lemma nearCoeffWeight_nonneg (q : ℤ × ℤ × ℤ × ℤ) : 0 ≤ nearCoeffWeight q :=
  mul_nonneg (mul_nonneg (mul_nonneg (cWeight_nonneg _) (cWeight_nonneg _))
    (cWeight_nonneg _)) (cWeight_nonneg _)

-- @node: nearCoeffWeight_summable
/-- [The fourfold coefficient weights have a finite sum over all integer
quadruples](goal). -/
lemma nearCoeffWeight_summable : Summable nearCoeffWeight := by
  unfold nearCoeffWeight
  simpa only [mul_assoc] using near_fourfold_summable
    cWeight cWeight cWeight cWeight
    cWeight_summable cWeight_summable cWeight_summable cWeight_summable
    cWeight_nonneg cWeight_nonneg cWeight_nonneg cWeight_nonneg

-- @node: nearCoeffWeight_tsum
/-- [The sum of the fourfold coefficient weights equals the fourth power of S₀,
the sum of the single-index weights](goal). -/
lemma nearCoeffWeight_tsum : (∑' q, nearCoeffWeight q) = S0 ^ 4 := by
  have h := near_fourfold_tsum cWeight cWeight cWeight cWeight
    cWeight_summable cWeight_summable cWeight_summable cWeight_summable
    cWeight_nonneg cWeight_nonneg cWeight_nonneg cWeight_nonneg
  simp only [nearCoeffWeight, mul_assoc] at ⊢
  rw [h]
  change S0 * (S0 * (S0 * S0)) = S0 ^ 4
  ring

-- @node: nearCoeffDiag_block_norm_le
/-- If [A is a circle family for π](hyp:hπ), then [the norm of the product of its
k-th coefficient on the first tree factor and its m-th coefficient on the second,
at group pair x, is at most the product of the weights at k and m](goal). -/
lemma nearCoeffDiag_block_norm_le (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (k m : ℤ) (x : ProdGrp) :
    ‖ampFst (D := D) (A k x.1) * ampSnd (D := D) (A m x.2)‖ ≤
      cWeight k * cWeight m := by
  apply (norm_mul_le _ _).trans
  exact mul_le_mul ((amplify_spec (A k x.1)).2.trans (hπ.2.1 k x.1))
    ((lp.norm_mapCLM_le 2 _ (norm_nonneg _) _).trans (hπ.2.1 m x.2))
    (norm_nonneg _) (cWeight_nonneg k)

-- @node: nearCoeffDiag
/-- For [a Hilbert space D](hyp:D), [a circle representation π](hyp:π), [Laurent coefficient data A](hyp:A)
[forming a circle family for π](hyp:hπ), and [integer indices k and m](hyp:k,m),
the [diagonal coefficient operator](goal) applies the k-th coefficient of A to the
first tree factor and the m-th coefficient to the second at each group pair. -/
noncomputable def nearCoeffDiag (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (k m : ℤ) : Hsp D →L[ℂ] Hsp D :=
  lp.mapCLM 2 (fun x : ProdGrp => ampFst (A k x.1) * ampSnd (A m x.2))
    (mul_nonneg (cWeight_nonneg k) (cWeight_nonneg m))
    (nearCoeffDiag_block_norm_le π A hπ k m)

-- @node: nearCoeffDiag_norm_le
/-- If [A is a circle family for π](hyp:hπ), then [the norm of its diagonal
coefficient operator at k and m is at most the product of their scalar
coefficient weights](goal). -/
lemma nearCoeffDiag_norm_le (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (k m : ℤ) :
    ‖nearCoeffDiag (D := D) π A hπ k m‖ ≤ cWeight k * cWeight m := by
  exact lp.norm_mapCLM_le 2 _ _ _

-- @node: nearCoeffBlock
/-- For [a Hilbert space D](hyp:D), [a circle representation π](hyp:π), [Laurent data A](hyp:A)
[forming a circle family for π](hyp:hπ), [an operator X on the scalar sequence
space](hyp:X), and [four integer indices q, ordered as k, m, p, j](hyp:q),
the [coefficient block](goal) is the diagonal coefficient at k and m, followed by
the amplification of X and the adjoint diagonal coefficient at j and p. -/
noncomputable def nearCoeffBlock (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (X : Ssp →L[ℂ] Ssp)
    (q : ℤ × ℤ × ℤ × ℤ) : Hsp D →L[ℂ] Hsp D :=
  nearCoeffDiag (D := D) π A hπ q.1 q.2.1 * amplify (E := Lsp D) X *
    star (nearCoeffDiag (D := D) π A hπ q.2.2.2 q.2.2.1)

-- @node: nearCoeffBlock_norm_le
/-- If [A is a circle family for π](hyp:hπ), then [the norm of the coefficient
block for X at q is at most the fourfold coefficient weight at q times the
operator norm of X](goal). -/
lemma nearCoeffBlock_norm_le (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (X : Ssp →L[ℂ] Ssp)
    (q : ℤ × ℤ × ℤ × ℤ) :
    ‖nearCoeffBlock (D := D) π A hπ X q‖ ≤ nearCoeffWeight q * ‖X‖ := by
  have hleft : ‖nearCoeffDiag (D := D) π A hπ q.1 q.2.1 * amplify X‖ ≤
      (cWeight q.1 * cWeight q.2.1) * ‖X‖ :=
    (norm_mul_le _ _).trans (mul_le_mul (nearCoeffDiag_norm_le (D := D) π A hπ _ _)
      (amplify_spec X).2 (norm_nonneg _)
      (mul_nonneg (cWeight_nonneg _) (cWeight_nonneg _)))
  calc
    _ ≤ ‖nearCoeffDiag (D := D) π A hπ q.1 q.2.1 * amplify X‖ *
        ‖star (nearCoeffDiag (D := D) π A hπ q.2.2.2 q.2.2.1)‖ := norm_mul_le _ _
    _ ≤ ((cWeight q.1 * cWeight q.2.1) * ‖X‖) *
        (cWeight q.2.2.2 * cWeight q.2.2.1) :=
      mul_le_mul hleft (by simpa only [norm_star] using
        (nearCoeffDiag_norm_le (D := D) π A hπ q.2.2.2 q.2.2.1)) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (cWeight_nonneg _) (cWeight_nonneg _)) (norm_nonneg _))
    _ = _ := by unfold nearCoeffWeight; ring

-- @node: nearZTerm
/-- For [a Hilbert space D](hyp:D), [an operator coefficient family B indexed by integer quadruples](hyp:B),
[operators U and V on D](hyp:U,V), and [indices q ordered as k, m, p, j](hyp:q),
the [original expansion term](goal) is B at q multiplied by the pointwise
amplification of U to power k, V to power m minus p, and U to power minus j,
in that order. -/
noncomputable def nearZTerm (B : (ℤ × ℤ × ℤ × ℤ) → (Hsp D →L[ℂ] Hsp D))
    (U V : D →L[ℂ] D) (q : ℤ × ℤ × ℤ × ℤ) : Hsp D →L[ℂ] Hsp D :=
  B q * nearMatrixAmp (unitaryIntPow U q.1 * unitaryIntPow V (q.2.1 - q.2.2.1) *
    unitaryIntPow U (-q.2.2.2))

-- @node: nearYTerm
/-- For [a Hilbert space D](hyp:D), [an operator coefficient family B indexed by integer quadruples](hyp:B),
[operators U and V on D](hyp:U,V), and [indices q ordered as k, m, p, j](hyp:q),
the [reordered expansion term](goal) is B at q multiplied by the pointwise
amplification of U to power k minus j followed by V to power m minus p. -/
noncomputable def nearYTerm (B : (ℤ × ℤ × ℤ × ℤ) → (Hsp D →L[ℂ] Hsp D))
    (U V : D →L[ℂ] D) (q : ℤ × ℤ × ℤ × ℤ) : Hsp D →L[ℂ] Hsp D :=
  B q * nearMatrixAmp (unitaryIntPow U (q.1 - q.2.2.2) *
    unitaryIntPow V (q.2.1 - q.2.2.1))

-- @node: near_matrix_product_norm_le_one
/-- If [U is unitary](hyp:hU) and [V is unitary](hyp:hV), then [the product of
their integer powers with exponents a and b has operator norm at most one](goal). -/
lemma near_matrix_product_norm_le_one (U V : D →L[ℂ] D)
    (hU : U ∈ unitary _) (hV : V ∈ unitary _) (a b : ℤ) :
    ‖unitaryIntPow U a * unitaryIntPow V b‖ ≤ 1 := by
  exact (norm_mul_le _ _).trans (by
    simpa using mul_le_mul (unitaryIntPow_norm_le U hU a)
      (unitaryIntPow_norm_le V hV b) (norm_nonneg _) zero_le_one)

-- @node: nearZTerm_norm_le
/-- If [U is unitary](hyp:hU) and [V is unitary](hyp:hV), then [the original
expansion term at q has norm at most the norm of its coefficient B at q](goal). -/
lemma nearZTerm_norm_le (B : (ℤ × ℤ × ℤ × ℤ) → (Hsp D →L[ℂ] Hsp D))
    (U V : D →L[ℂ] D) (hU : U ∈ unitary _) (hV : V ∈ unitary _)
    (q : ℤ × ℤ × ℤ × ℤ) : ‖nearZTerm B U V q‖ ≤ ‖B q‖ := by
  have hp : ‖unitaryIntPow U q.1 * unitaryIntPow V (q.2.1 - q.2.2.1) *
      unitaryIntPow U (-q.2.2.2)‖ ≤ 1 :=
    (norm_mul_le _ _).trans (by
      simpa using mul_le_mul (near_matrix_product_norm_le_one U V hU hV _ _)
        (unitaryIntPow_norm_le U hU _) (norm_nonneg _) zero_le_one)
  exact (norm_mul_le _ _).trans (by
    simpa using mul_le_mul_of_nonneg_left ((nearMatrixAmp_norm_le _).trans hp) (norm_nonneg (B q)))

-- @node: nearYTerm_norm_le
/-- If [U is unitary](hyp:hU) and [V is unitary](hyp:hV), then [the reordered
expansion term at q has norm at most the norm of its coefficient B at q](goal). -/
lemma nearYTerm_norm_le (B : (ℤ × ℤ × ℤ × ℤ) → (Hsp D →L[ℂ] Hsp D))
    (U V : D →L[ℂ] D) (hU : U ∈ unitary _) (hV : V ∈ unitary _)
    (q : ℤ × ℤ × ℤ × ℤ) : ‖nearYTerm B U V q‖ ≤ ‖B q‖ := by
  exact (norm_mul_le _ _).trans (by
    simpa using mul_le_mul_of_nonneg_left
      ((nearMatrixAmp_norm_le _).trans (near_matrix_product_norm_le_one U V hU hV _ _))
      (norm_nonneg (B q)))

-- @node: near_laurent_series_absConv
/-- If [U is unitary](hyp:hU), [V is unitary](hyp:hV), and [each coefficient B at q
has norm at most R times the fourfold coefficient weight at q](hyp:hB), then
[both the original and reordered operator expansions converge absolutely](goal). -/
lemma near_laurent_series_absConv
    (B : (ℤ × ℤ × ℤ × ℤ) → (Hsp D →L[ℂ] Hsp D))
    (U V : D →L[ℂ] D) (hU : U ∈ unitary _) (hV : V ∈ unitary _)
    (R : ℝ) (hB : ∀ q, ‖B q‖ ≤ nearCoeffWeight q * R) :
    Summable (fun q => ‖nearZTerm B U V q‖) ∧
      Summable (fun q => ‖nearYTerm B U V q‖) := by
  constructor
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => (nearZTerm_norm_le B U V hU hV q).trans (hB q))
      (nearCoeffWeight_summable.mul_right R)
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => (nearYTerm_norm_le B U V hU hV q).trans (hB q))
      (nearCoeffWeight_summable.mul_right R)

-- @node: near_laurent_series_reordering_le
/-- If [U is unitary](hyp:hU), [V is unitary](hyp:hV), and [each coefficient B at q
has norm at most R times the fourfold coefficient weight at q](hyp:hB), then
[the norm of the difference between the original and reordered series is at most
the constant nearC times the norm of UV minus VU times R](goal). -/
lemma near_laurent_series_reordering_le
    (B : (ℤ × ℤ × ℤ × ℤ) → (Hsp D →L[ℂ] Hsp D))
    (U V : D →L[ℂ] D) (hU : U ∈ unitary _) (hV : V ∈ unitary _)
    (R : ℝ) (hB : ∀ q, ‖B q‖ ≤ nearCoeffWeight q * R) :
    ‖(∑' q, nearZTerm B U V q) - ∑' q, nearYTerm B U V q‖ ≤
      nearC * ‖U * V - V * U‖ * R := by
  obtain ⟨hZ, hY⟩ := near_laurent_series_absConv B U V hU hV R hB
  rw [← hZ.of_norm.tsum_sub hY.of_norm]
  have hterm (q : ℤ × ℤ × ℤ × ℤ) :
      ‖nearZTerm B U V q - nearYTerm B U V q‖ ≤
        nearWeight q * (‖U * V - V * U‖ * R) := by
    rw [nearZTerm, nearYTerm, ← mul_sub, ← nearMatrixAmp_sub]
    calc
      _ ≤ ‖B q‖ * ‖nearMatrixAmp
          (unitaryIntPow U q.1 * unitaryIntPow V (q.2.1 - q.2.2.1) *
            unitaryIntPow U (-q.2.2.2) -
          unitaryIntPow U (q.1 - q.2.2.2) * unitaryIntPow V (q.2.1 - q.2.2.1))‖ :=
        norm_mul_le _ _
      _ ≤ (nearCoeffWeight q * R) *
          (((q.2.1 - q.2.2.1).natAbs : ℝ) * (q.2.2.2.natAbs : ℝ) * ‖U * V - V * U‖) :=
        mul_le_mul (hB q)
          ((nearMatrixAmp_norm_le _).trans (near_laurent_reordering_le U V hU hV _ _ _ _))
          (norm_nonneg _) ((norm_nonneg (B q)).trans (hB q))
      _ = _ := by unfold nearCoeffWeight nearWeight; ring
  have hsum := (nearWeight_summable.mul_right (‖U * V - V * U‖ * R)).hasSum
  have hbound := tsum_of_norm_bounded hsum hterm
  simpa only [tsum_mul_right, nearC, mul_assoc] using hbound

end Papers.OaiNearInclusionsVon
