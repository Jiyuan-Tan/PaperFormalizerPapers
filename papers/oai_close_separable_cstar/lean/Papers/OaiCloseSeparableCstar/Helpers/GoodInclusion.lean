module

public import Papers.OaiCloseSeparableCstar.Helpers.Ambient
public import Papers.OaiCloseSeparableCstar.Helpers.Invariant
public import Papers.OaiCloseSeparableCstar.Helpers.TensorLp

/-! # Lemma 8: the undeformed inclusion has the spatial tensor-norm identity -/

public section

open scoped BigOperators

namespace Papers.OaiCloseSeparableCstar

/-- [Exchanging the two regular Hilbert coordinates preserves the norm of every
vector](goal). -/
-- @node: flipOp_norm
lemma flipOp_norm (v : LSp) : ‖flipOp v‖ = ‖v‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
  congr 1
  simp_rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)]
  exact (hilbertSum_summable_coordinates v).tsum_comm

/-- [The operator exchanging the two regular Hilbert coordinates is unitary](goal). -/
-- @node: flipOp_mem_unitary
lemma flipOp_mem_unitary : flipOp ∈ unitary (Op LSp) := by
  let u : (Op LSp)ˣ :=
    { val := flipOp
      inv := flipOp
      val_inv := flipOp_mul_self
      inv_val := flipOp_mul_self }
  apply IsUnit.mem_unitary_of_star_mul_self ⟨u, rfl⟩
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact flipOp.norm_map_iff_adjoint_comp_self.mp flipOp_norm

/-- [The adjoint of the coordinate exchange is the coordinate exchange itself](goal). -/
-- @node: flipOp_star
lemma flipOp_star : star flipOp = flipOp := by
  calc
    star flipOp = star flipOp * (flipOp * flipOp) := by rw [flipOp_mul_self, mul_one]
    _ = flipOp := by
      rw [← mul_assoc, Unitary.star_mul_self_of_mem flipOp_mem_unitary, one_mul]

/-- [Applying a constant diagonal operator to a vector supported at one group
coordinate keeps that support and applies the underlying operator to the vector
at that coordinate](goal). -/
-- @node: constantDiagOp_single
lemma constantDiagOp_single (X : Op KSp) (x : FG) (w : KSp) :
    constantDiagOp (I := FG) X (lp.single 2 x w) = lp.single 2 x (X w) := by
  classical
  ext i
  by_cases hi : i = x
  · subst i
    simp [constantDiagOp, diagOp]
  · simp [constantDiagOp, diagOp, lp.single_apply, hi]

/-- [The operator applying the same bounded operator at every group coordinate
has exactly the norm of that underlying operator](goal). -/
-- @node: constantDiagOp_norm
lemma constantDiagOp_norm (X : Op KSp) : ‖constantDiagOp (I := FG) X‖ = ‖X‖ := by
  apply le_antisymm
  · unfold constantDiagOp diagOp
    apply LinearMap.mkContinuous_norm_le
    exact norm_nonneg X
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro w
    have h := (constantDiagOp (I := FG) X).le_opNorm (lp.single 2 (1 : FG) w)
    simpa only [constantDiagOp_single, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
      using h

/-- [Conjugating the constant diagonal extension of a bounded operator by the
coordinate exchange gives an operator with exactly the norm of the original
bounded operator](goal). -/
-- @node: firstFactorOp_norm
lemma firstFactorOp_norm (Y : Op KSp) :
    ‖flipOp * constantDiagOp Y * flipOp‖ = ‖Y‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ flipOp_mem_unitary,
    CStarRing.norm_mem_unitary_mul _ flipOp_mem_unitary, constantDiagOp_norm]

/-- [The untwisting operator obtained by conjugating the adjoint of the undeformed
absorption operator by the coordinate exchange is unitary](goal). -/
-- @node: goodUntwist_mem_unitary
lemma goodUntwist_mem_unitary :
    flipOp * star (absorptionOp piZero) * flipOp ∈ unitary (Op LSp) := by
  exact mul_mem (mul_mem flipOp_mem_unitary
    (Unitary.star_mem (absorption piZero KSp_nontrivial).1)) flipOp_mem_unitary

/-- [Conjugating an undeformed representation operator by the coordinate exchange
leaves it unchanged](goal). -/
-- @node: flip_Qzero_flip
lemma flip_Qzero_flip (g : FG) : flipOp * Qop piZero g * flipOp = Qop piZero g := by
  ext v x y
  rfl

/-- [Conjugating the undeformed representation operator of any group element by
the untwisting unitary gives left translation by that element on the second
Hilbert factor](goal). -/
-- @node: goodUntwist_generator
lemma goodUntwist_generator (g : FG) :
    (flipOp * star (absorptionOp piZero) * flipOp) * Qop piZero g *
      star (flipOp * star (absorptionOp piZero) * flipOp) =
        constantDiagOp (leftReg g : Op KSp) := by
  have hu := (absorption piZero KSp_nontrivial).1
  have hg := (absorption piZero KSp_nontrivial).2 g
  have hinv : star (absorptionOp piZero) * Qop piZero g * absorptionOp piZero =
      shiftOp g := by
    change absorptionOp piZero * shiftOp g * star (absorptionOp piZero) =
      Qop piZero g at hg
    rw [← hg]
    simp only [mul_assoc, ← mul_assoc (star (absorptionOp piZero)) (absorptionOp piZero),
      Unitary.star_mul_self_of_mem hu, one_mul, mul_one]
  rw [star_mul, star_mul, flipOp_star, star_star]
  calc
    _ = flipOp * (star (absorptionOp piZero) *
        (flipOp * Qop piZero g * flipOp) * absorptionOp piZero) * flipOp := by
      simp only [mul_assoc]
    _ = flipOp * shiftOp g * flipOp := by rw [flip_Qzero_flip, hinv]
    _ = _ := flip_shiftOp_flip g

/-- If [an operator commutes with every element of the ambient algebra associated
with the given representation](hyp:hz), then [it commutes with the untwisting
unitary](goal). -/
-- @node: goodUntwist_commutes
lemma goodUntwist_commutes (π : FG →* unitary (Op KSp))
    {z : Op LSp} (hz : z ∈ commutant (Dalg π)) :
    (flipOp * star (absorptionOp piZero) * flipOp) * z =
      z * (flipOp * star (absorptionOp piZero) * flipOp) := by
  rw [Dalg_commutant_eq] at hz
  obtain ⟨Y, hY, rfl⟩ := hz
  have hc : star (absorptionOp piZero) * constantDiagOp Y =
      constantDiagOp Y * star (absorptionOp piZero) := by
    apply ContinuousLinearMap.ext
    intro v
    apply lp.ext
    funext x
    change (star (absorptionOp piZero) (constantDiagOp Y v)) x =
      Y ((star (absorptionOp piZero) v) x)
    simp only [absorptionOp, diagUnitaryOp_star_apply]
    have h : (leftReg x⁻¹ : Op KSp) * Y = Y * (leftReg x⁻¹ : Op KSp) :=
      hY _ ⟨x⁻¹, rfl⟩
    have hx : (leftReg x⁻¹ : Op KSp) = star (leftReg x : Op KSp) := by
      rw [map_inv, ← Unitary.star_eq_inv]
      rfl
    rw [hx] at h
    exact congrArg (fun A : Op KSp => A (v x)) h
  simpa only [mul_assoc, ← mul_assoc flipOp flipOp, flipOp_mul_self, one_mul] using
    congrArg (fun A : Op LSp => flipOp * A * flipOp) hc

/-- [Conjugation by the untwisting unitary maps the closed undeformed algebra
onto the norm-closed complex star algebra generated by left translations acting
on the second Hilbert factor](goal). -/
-- @node: goodUntwist_conj_Palg
lemma goodUntwist_conj_Palg :
    conjSet (flipOp * star (absorptionOp piZero) * flipOp) (Palg piZero) =
      ((StarAlgebra.adjoin ℂ
        (Set.range (fun g => constantDiagOp (I := FG) (leftReg g : Op KSp)))).topologicalClosure :
          Set (Op LSp)) := by
  let U : unitary (Op LSp) := ⟨_, goodUntwist_mem_unitary⟩
  let e := Unitary.conjStarAlgAut ℂ (Op LSp) U
  have hc : Continuous e := by
    change Continuous (fun x : Op LSp => (U : Op LSp) * x * star (U : Op LSp))
    fun_prop
  have hci : Continuous e.symm := by
    change Continuous (fun x : Op LSp => star (U : Op LSp) * x * (U : Op LSp))
    fun_prop
  let h : Op LSp ≃ₜ Op LSp :=
    { e.toEquiv with continuous_toFun := hc, continuous_invFun := hci }
  have he : IsClosedMap e := h.isClosedMap
  have hr : e '' Set.range (Qop piZero) =
      Set.range (fun g => constantDiagOp (I := FG) (leftReg g : Op KSp)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, (goodUntwist_generator g).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨Qop piZero g, ⟨g, rfl⟩, goodUntwist_generator g⟩
  change ((Palg piZero).map e.toStarAlgHom : Set (Op LSp)) = _
  rw [Palg, ← StarSubalgebra.topologicalClosure_map _ _ he hc,
    StarAlgHom.map_adjoin]
  change ((StarAlgebra.adjoin ℂ (e '' Set.range (Qop piZero))).topologicalClosure :
    Set (Op LSp)) = _
  rw [hr]

/-- If [an operator belongs to the commutant of the ambient algebra associated
with the given representation](hyp:hz), then [conjugation by the untwisting
unitary leaves that operator unchanged](goal). -/
-- @node: goodUntwist_fixes_commutant
lemma goodUntwist_fixes_commutant (π : FG →* unitary (Op KSp))
    {z : Op LSp} (hz : z ∈ commutant (Dalg π)) :
    (flipOp * star (absorptionOp piZero) * flipOp) * z *
      star (flipOp * star (absorptionOp piZero) * flipOp) = z := by
  rw [goodUntwist_commutes π hz, mul_assoc,
    Unitary.mul_star_self_of_mem goodUntwist_mem_unitary, mul_one]

/-- If [each operator in the second finite family belongs to the commutant of
the ambient algebra associated with the given representation](hyp:hz), then
[the norm of the sum of paired products is unchanged when every operator in
the first family is conjugated by the untwisting unitary](goal). -/
-- @node: goodUntwist_product_norm
lemma goodUntwist_product_norm (π : FG →* unitary (Op KSp))
    {m : ℕ} (p z : Fin m → Op LSp) (hz : ∀ i, z i ∈ commutant (Dalg π)) :
    ‖∑ i, p i * z i‖ =
      ‖∑ i, ((flipOp * star (absorptionOp piZero) * flipOp) * p i *
        star (flipOp * star (absorptionOp piZero) * flipOp)) * z i‖ := by
  classical
  let U := flipOp * star (absorptionOp piZero) * flipOp
  have hU : U ∈ unitary (Op LSp) := goodUntwist_mem_unitary
  have he : U * (∑ i, p i * z i) * star U =
      ∑ i, (U * p i * star U) * z i := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    have hi : U * z i * star U = z i := goodUntwist_fixes_commutant π (hz i)
    calc
      U * (p i * z i) * star U =
          (U * p i * star U) * (U * z i * star U) := by
        simp only [mul_assoc, ← mul_assoc (star U) U,
          Unitary.star_mul_self_of_mem hU, one_mul]
      _ = _ := by rw [hi]
  rw [← he, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU),
    CStarRing.norm_mem_unitary_mul _ hU]

/-- If [each operator in the second finite family belongs to the commutant of
the ambient algebra associated with the given representation](hyp:hz), then
[conjugating every operator in the first family by the untwisting unitary leaves
the spatial norm of their paired tensor sum unchanged](goal). -/
-- @node: goodUntwist_tensor_norm
lemma goodUntwist_tensor_norm (π : FG →* unitary (Op KSp))
    {m : ℕ} (p z : Fin m → Op LSp) (hz : ∀ i, z i ∈ commutant (Dalg π)) :
    tensorSumNorm (fun i => (flipOp * star (absorptionOp piZero) * flipOp) * p i *
      star (flipOp * star (absorptionOp piZero) * flipOp)) z = tensorSumNorm p z := by
  let U : unitary (Op LSp) := ⟨_, goodUntwist_mem_unitary⟩
  have he : (fun i => (U : Op LSp) * z i * star (U : Op LSp)) = z := by
    funext i
    exact goodUntwist_fixes_commutant π (hz i)
  simpa only [he] using tensorSumNorm_conjugate U p z

/-- If [a bounded operator commutes with every matrix unit acting on the first
Hilbert factor](hyp:hT), then [it is the constant diagonal extension of some
bounded operator on the second factor](goal). -/
-- @node: firstMatrixUnit_commutant_factorization
lemma firstMatrixUnit_commutant_factorization (T : Op LSp)
    (hT : ∀ x y, (flipOp * constantDiagOp (matUnit x y) * flipOp) * T =
      T * (flipOp * constantDiagOp (matUnit x y) * flipOp)) :
    ∃ X : Op KSp, T = constantDiagOp X := by
  have hflip (x y : FG) :
      constantDiagOp (matUnit x y) * (flipOp * T * flipOp) =
        (flipOp * T * flipOp) * constantDiagOp (matUnit x y) := by
    have h := congrArg (fun A : Op LSp => flipOp * A * flipOp) (hT x y)
    simpa only [mul_assoc, ← mul_assoc flipOp flipOp, flipOp_mul_self,
      one_mul, mul_one] using h
  obtain ⟨X, hX⟩ := matrixUnit_commutant_factorization (flipOp * T * flipOp) hflip
  refine ⟨X, ?_⟩
  have h := congrArg (fun A : Op LSp => flipOp * A * flipOp) hX
  simpa only [mul_assoc, ← mul_assoc flipOp flipOp, flipOp_mul_self,
    one_mul, mul_one] using h

/-- If [an operator belongs to the norm-closed complex star algebra generated
by left translations on the second Hilbert factor](hyp:hT), then [it is the
constant diagonal extension of a bounded operator on that factor](goal). -/
-- @node: secondRegularAlgebra_factorization
lemma secondRegularAlgebra_factorization {T : Op LSp}
    (hT : T ∈ (StarAlgebra.adjoin ℂ
      (Set.range (fun g => constantDiagOp (I := FG) (leftReg g : Op KSp)))).topologicalClosure) :
    ∃ X : Op KSp, T = constantDiagOp X := by
  apply firstMatrixUnit_commutant_factorization T
  intro x y
  have hm : flipOp * constantDiagOp (matUnit x y) * flipOp ∈
      StarSubalgebra.centralizer ℂ
        (Set.range (fun g => constantDiagOp (I := FG) (leftReg g : Op KSp))) := by
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    constructor
    · exact firstFactor_commutes_constant _ _
    · rw [constantDiagOp_star]
      exact firstFactor_commutes_constant _ _
  have h := StarSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer ℂ _ hT
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp h _ hm).1

/-- If [an operator belongs to the closed undeformed algebra](hyp:hp), then
[its conjugate by the untwisting unitary is the constant diagonal extension
of some bounded operator on the second Hilbert factor](goal). -/
-- @node: goodUntwist_factorization
lemma goodUntwist_factorization {p : Op LSp} (hp : p ∈ Palg piZero) :
    ∃ X : Op KSp, (flipOp * star (absorptionOp piZero) * flipOp) * p *
      star (flipOp * star (absorptionOp piZero) * flipOp) = constantDiagOp X := by
  apply secondRegularAlgebra_factorization
  have hi : (flipOp * star (absorptionOp piZero) * flipOp) * p *
      star (flipOp * star (absorptionOp piZero) * flipOp) ∈
      conjSet (flipOp * star (absorptionOp piZero) * flipOp) (Palg piZero) :=
    ⟨p, hp, rfl⟩
  rw [goodUntwist_conj_Palg] at hi
  exact hi

/-- If [a complex linear isometry has dense range](hyp:he) and [applying it
after the operator on its domain agrees with applying the operator on its
codomain after it](hyp:h), then [the two bounded operators have equal norms](goal). -/
-- @node: norm_eq_of_dense_isometric_intertwiner
lemma norm_eq_of_dense_isometric_intertwiner
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (e : E →ₗᵢ[ℂ] F) (he : DenseRange e) (A : Op E) (B : Op F)
    (h : ∀ x, e (A x) = B (e x)) : ‖A‖ = ‖B‖ := by
  apply le_antisymm
  · apply A.opNorm_le_bound (norm_nonneg B)
    intro x
    rw [← e.norm_map (A x), h]
    simpa only [e.norm_map] using B.le_opNorm (e x)
  · apply B.opNorm_le_bound (norm_nonneg A)
    apply isClosed_property he (isClosed_le (by fun_prop) (by fun_prop))
    intro x
    rw [← h, e.norm_map, e.norm_map]
    exact A.le_opNorm x

/-- [Exchanging coordinates in the square-summable realization of a pure
tensor gives the realization of the pure tensor with its factors reversed](goal). -/
-- @node: scalarLpTensor_flip
lemma scalarLpTensor_flip (a b : KSp) :
    flipOp (scalarLpTensor (a ⊗ₜ[ℂ] b)) = scalarLpTensor (b ⊗ₜ[ℂ] a) := by
  ext x y
  change a y * b x = b x * a y
  exact mul_comm _ _

/-- [Applying a constant diagonal operator to the square-summable realization
of a pure tensor gives the realization obtained by applying the underlying
operator to the second tensor factor](goal). -/
-- @node: scalarLpTensor_constantDiag
lemma scalarLpTensor_constantDiag (X : Op KSp) (a b : KSp) :
    constantDiagOp X (scalarLpTensor (a ⊗ₜ[ℂ] b)) =
      scalarLpTensor (a ⊗ₜ[ℂ] X b) := by
  ext x y
  change (X (a x • b)) y = (a x • X b) y
  rw [map_smul]

/-- [Applying a constant diagonal operator conjugated by coordinate exchange
to the square-summable realization of a pure tensor gives the realization obtained
by applying the underlying operator to the first tensor factor](goal). -/
-- @node: scalarLpTensor_firstFactor
lemma scalarLpTensor_firstFactor (Y : Op KSp) (a b : KSp) :
    (flipOp * constantDiagOp Y * flipOp : Op LSp) (scalarLpTensor (a ⊗ₜ[ℂ] b)) =
      scalarLpTensor (Y a ⊗ₜ[ℂ] b) := by
  change flipOp (constantDiagOp Y (flipOp (scalarLpTensor (a ⊗ₜ[ℂ] b)))) = _
  rw [scalarLpTensor_flip, scalarLpTensor_constantDiag, scalarLpTensor_flip]

/-- [The norm of the sum of paired products of second-factor and first-factor
operators equals the norm of the sum of tensor-product operators, with each
first-factor operator preceding its paired second-factor operator](goal). -/
-- @node: independentFactor_product_norm
lemma independentFactor_product_norm {m : ℕ} (X Y : Fin m → Op KSp) :
    ‖∑ i, constantDiagOp (X i) * (flipOp * constantDiagOp (Y i) * flipOp)‖ =
      ‖∑ i, TensorProduct.mapL (Y i) (X i)‖ := by
  classical
  symm
  apply norm_eq_of_dense_isometric_intertwiner
    (scalarLpTensor (I := FG) (F := KSp)) scalarLpTensor_denseRange
  intro v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [sum_apply, map_sum, TensorProduct.mapL_tmul]
    apply Finset.sum_congr rfl
    intro i _
    change scalarLpTensor (Y i a ⊗ₜ[ℂ] X i b) =
      constantDiagOp (X i) ((flipOp * constantDiagOp (Y i) * flipOp : Op LSp)
        (scalarLpTensor (a ⊗ₜ[ℂ] b)))
    rw [scalarLpTensor_firstFactor, scalarLpTensor_constantDiag]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- If [a complex linear isometry has dense range](hyp:he), then [its tensor
product with itself also has dense range](goal). -/
-- @node: tensorSquare_denseRange
lemma tensorSquare_denseRange
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (e : E →ₗᵢ[ℂ] F) (he : DenseRange e) :
    DenseRange (TensorProduct.mapIsometry e e) := by
  let M := (TensorProduct.mapIsometry e e).toLinearMap.range
  intro x
  change x ∈ closure (M : Set _)
  change x ∈ M.topologicalClosure
  induction x using TensorProduct.induction_on with
  | zero => exact M.topologicalClosure.zero_mem
  | tmul a b =>
    apply isClosed_property2 (p := fun a b : F => (a ⊗ₜ[ℂ] b) ∈ M.topologicalClosure) he
      (M.isClosed_topologicalClosure.preimage
        (show Continuous (fun q : F × F => q.1 ⊗ₜ[ℂ] q.2) by fun_prop)) _ a b
    intro v w
    exact M.le_topologicalClosure ⟨v ⊗ₜ[ℂ] w, rfl⟩
  | add x y hx hy => exact M.topologicalClosure.add_mem hx hy

/-- If [the second Hilbert space contains a specified vector of norm one](hyp:hv),
then [tensoring a bounded operator on the first space with the identity on the
second preserves its operator norm](goal). -/
-- @node: norm_rTensor_unit
lemma norm_rTensor_unit
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (A : Op E) (v : F) (hv : ‖v‖ = 1) : ‖A.rTensor F‖ = ‖A‖ := by
  apply le_antisymm (ContinuousLinearMap.norm_rTensor_le _ _)
  apply A.opNorm_le_bound (norm_nonneg _)
  intro x
  simpa only [ContinuousLinearMap.rTensor_tmul, TensorProduct.norm_tmul, hv, mul_one]
    using (A.rTensor F).le_opNorm (x ⊗ₜ[ℂ] v)

/-- If [the additional Hilbert space contains a specified vector of norm one](hyp:hv),
then [tensoring its identity on the left of a bounded operator preserves that
operator's norm](goal). -/
-- @node: norm_lTensor_unit
lemma norm_lTensor_unit
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (A : Op E) (v : F) (hv : ‖v‖ = 1) : ‖A.lTensor F‖ = ‖A‖ := by
  apply le_antisymm (ContinuousLinearMap.norm_lTensor_le _ _)
  apply A.opNorm_le_bound (norm_nonneg _)
  intro x
  simpa only [ContinuousLinearMap.lTensor_tmul, TensorProduct.norm_tmul, hv, one_mul]
    using (A.lTensor F).le_opNorm (v ⊗ₜ[ℂ] x)

set_option maxHeartbeats 800000 in
-- Four nested algebraic tensor maps require additional elaboration reductions.
/-- [The spatial norm of the tensor sum pairing constant diagonal operators
with coordinate-exchanged constant diagonal operators equals the norm of the
two-factor tensor sum with the latter underlying operators on the first factor
and the former underlying operators on the second](goal). -/
-- @node: independentFactor_tensor_norm
lemma independentFactor_tensor_norm {m : ℕ} (X Y : Fin m → Op KSp) :
    tensorSumNorm (fun i => constantDiagOp (X i))
      (fun i => flipOp * constantDiagOp (Y i) * flipOp) =
        ‖∑ i, TensorProduct.mapL (Y i) (X i)‖ := by
  classical
  let H := TensorProduct ℂ KSp KSp
  let A : Op H := ∑ i, TensorProduct.mapL (Y i) (X i)
  let B : Op (TensorProduct ℂ LSp LSp) :=
    ∑ i, TensorProduct.mapL (constantDiagOp (X i))
      (flipOp * constantDiagOp (Y i) * flipOp)
  let e := scalarLpTensor (I := FG) (F := KSp)
  let f := TensorProduct.mapIsometry e e
  let u : TensorProduct ℂ H H ≃ₗᵢ[ℂ]
      TensorProduct ℂ KSp (TensorProduct ℂ H KSp) :=
    (TensorProduct.assocIsometry ℂ KSp KSp H).trans
      (((TensorProduct.assocIsometry ℂ KSp KSp KSp).symm).lTensor KSp)
    |>.trans (((TensorProduct.commIsometry ℂ KSp KSp).rTensor KSp).lTensor KSp)
  let C := (A.rTensor KSp).lTensor KSp
  let D : Op (TensorProduct ℂ H H) :=
    u.symm.toLinearIsometry.toContinuousLinearMap ∘L C ∘L u.toLinearIsometry.toContinuousLinearMap
  have hu (a b c d : KSp) :
      u ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) =
        a ⊗ₜ[ℂ] ((c ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] d) := by
    simp [u, H, LinearIsometryEquiv.lTensor_def, LinearIsometryEquiv.rTensor_def]
  have hD : ∀ x, f (D x) = B (f x) := by
    suffices h : f.toLinearMap.comp D.toLinearMap =
        B.toLinearMap.comp f.toLinearMap by
      intro x
      exact congrArg (fun T => T x) h
    apply TensorProduct.ext_fourfold'
    intro a b c d
    change f (u.symm (C (u ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))))) = _
    rw [hu]
    simp only [C, ContinuousLinearMap.lTensor_tmul, ContinuousLinearMap.rTensor_tmul,
      A, sum_apply, TensorProduct.sum_tmul,
      TensorProduct.tmul_sum, map_sum]
    change (∑ i, e (a ⊗ₜ[ℂ] X i b) ⊗ₜ[ℂ] e (Y i c ⊗ₜ[ℂ] d)) =
      B (e (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] e (c ⊗ₜ[ℂ] d))
    simp only [B, sum_apply, TensorProduct.mapL_tmul, e,
      scalarLpTensor_constantDiag, scalarLpTensor_firstFactor]
  have hDB : ‖D‖ = ‖B‖ := norm_eq_of_dense_isometric_intertwiner f
    (tensorSquare_denseRange e scalarLpTensor_denseRange) D B hD
  have hDC : ‖D‖ = ‖C‖ := by
    apply norm_eq_of_dense_isometric_intertwiner u.toLinearIsometry u.surjective.denseRange
    intro x
    exact u.apply_symm_apply _
  have hv : ‖delta (1 : FG)‖ = 1 := by
    simp [delta, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  rw [tensorSumNorm_eq_opNorm]
  change ‖B‖ = ‖A‖
  rw [← hDB, hDC]
  exact (norm_lTensor_unit (A.rTensor KSp) (delta 1) hv).trans
    (norm_rTensor_unit A (delta 1) hv)

-- @node: lem:good-inclusion
/-- If [the deformation parameter lies strictly between zero and one](hyp:ht)
and [the unitary representation has generator coefficients equal to that parameter
and satisfies the tree representation's uniform approximation bound](hyp:hπ), then
[for every positive finite number of operators from the closed undeformed algebra
paired with operators from the commutant of the ambient algebra, the norm of their
sum of products equals the spatial norm of their tensor sum](goal). -/
lemma goodInclusion (t : ℝ) (ht : DeformationRange t)
    (π : FG →* unitary (Op KSp)) (hπ : IsTreeRep t ht π) :
    HasSpatialTensorIdentity (Dalg π) (Palg piZero) := by
  intro m hm p z hp hz
  let U := flipOp * star (absorptionOp piZero) * flipOp
  let q : Fin m → Op LSp := fun i => U * p i * star U
  have hq : ∀ i, q i ∈
      (StarAlgebra.adjoin ℂ
        (Set.range (fun g =>
          constantDiagOp (I := FG) (leftReg g : Op KSp)))).topologicalClosure := by
    intro i
    have hi : q i ∈ conjSet U (Palg piZero) := ⟨p i, hp i, rfl⟩
    rw [goodUntwist_conj_Palg] at hi
    exact hi
  rw [goodUntwist_product_norm π p z hz, ← goodUntwist_tensor_norm π p z hz]
  change ‖∑ i, q i * z i‖ = tensorSumNorm q z
  choose X hX using fun i => secondRegularAlgebra_factorization (hq i)
  have hY : ∀ i, ∃ Y : Op KSp, z i = flipOp * constantDiagOp Y * flipOp := by
    intro i
    obtain ⟨Y, _, he⟩ := (Dalg_commutant_eq π ▸ hz i)
    exact ⟨Y, he⟩
  choose Y hY using hY
  rw [show q = (fun i => constantDiagOp (X i)) from funext hX,
    show z = (fun i => flipOp * constantDiagOp (Y i) * flipOp) from funext hY]
  rw [independentFactor_product_norm, independentFactor_tensor_norm]

end Papers.OaiCloseSeparableCstar
