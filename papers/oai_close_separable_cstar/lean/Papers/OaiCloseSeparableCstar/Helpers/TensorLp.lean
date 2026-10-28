module

public import Papers.OaiCloseSeparableCstar.Helpers.Invariant

/-! # Coordinate realization of algebraic Hilbert tensors

The coordinate map is an isometry, including when the tensor fibers are not complete.
This permits tensor estimates to be transferred to Hilbert direct sums.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace

namespace Papers.OaiCloseSeparableCstar

variable {I E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

-- @node: lpTensorPure
/-- For [a square-summable family v](hyp:v) indexed by [I](hyp:I) in
[the complex inner product space E](hyp:E), and [a vector w](hyp:w) in
[the complex inner product space F](hyp:F), [the coordinatewise pure tensor family](goal)
has at each coordinate the tensor product of that coordinate of v with w; this family is square summable. -/
noncomputable def lpTensorPure (v : lp (fun _ : I => E) 2) (w : F) :
    lp (fun _ : I => TensorProduct ℂ E F) 2 :=
  ⟨fun i => v i ⊗ₜ[ℂ] w, by
    apply ((lp.memℓp v).norm.const_mul ‖w‖).mono
    intro i
    simp only [TensorProduct.norm_tmul, mul_comm, le_refl]⟩

-- @node: lpTensorLinear
/-- For [an index set I](hyp:I) and [complex inner product spaces E](hyp:E) and
[F](hyp:F), [the coordinate realization map](goal) is the complex linear map
from the algebraic tensor product of square-summable E-valued families with F
to square-summable families of tensors, sending a pure tensor of v and w
to the family whose i-th entry is the tensor product of v at i with w. -/
noncomputable def lpTensorLinear :
    TensorProduct ℂ (lp (fun _ : I => E) 2) F →ₗ[ℂ]
      lp (fun _ : I => TensorProduct ℂ E F) 2 :=
  TensorProduct.lift
    { toFun := fun v =>
        { toFun := lpTensorPure v
          map_add' := by
            intro a b
            ext i
            exact TensorProduct.tmul_add (v i) a b
          map_smul' := by
            intros
            ext i
            simp [lpTensorPure, TensorProduct.smul_tmul', TensorProduct.tmul_smul] }
      map_add' := by
        intro a b
        ext w i
        exact TensorProduct.add_tmul (a i) (b i) w
      map_smul' := by
        intros
        ext w i
        simp [lpTensorPure, TensorProduct.smul_tmul'] }

-- @node: lpTensorLinear_tmul
/-- For [a square-summable family v of vectors](hyp:v),
[the coordinate realization of its pure tensor with w has at coordinate i the tensor product of v at i with w](goal). -/
@[simp] lemma lpTensorLinear_tmul (v : lp (fun _ : I => E) 2) (w : F) (i : I) :
    lpTensorLinear (v ⊗ₜ[ℂ] w) i = v i ⊗ₜ[ℂ] w := rfl

-- @node: lpTensorLinear_inner
/-- For [two algebraic tensors x and y with square-summable first factors](hyp:x,y),
[the inner product of their coordinate realizations equals their original tensor inner product](goal). -/
lemma lpTensorLinear_inner (x y : TensorProduct ℂ (lp (fun _ : I => E) 2) F) :
    ⟪lpTensorLinear x, lpTensorLinear y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v' w' =>
      simp only [lp.inner_eq_tsum, lpTensorLinear_tmul, TensorProduct.inner_tmul]
      exact tsum_mul_right
    | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
  | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]

-- @node: lpTensorIsometry
/-- For [an index set I](hyp:I) and [complex inner product spaces E](hyp:E) and
[F](hyp:F), [the coordinate tensor embedding](goal) is the complex linear isometry
from the algebraic tensor product of square-summable E-valued families with F
into square-summable families of tensors, sending each pure tensor of v and w
to the family of tensor products of the entries of v with w. -/
noncomputable def lpTensorIsometry :
    TensorProduct ℂ (lp (fun _ : I => E) 2) F →ₗᵢ[ℂ]
      lp (fun _ : I => TensorProduct ℂ E F) 2 :=
  (lpTensorLinear (I := I) (E := E) (F := F)).isometryOfInner
    (lpTensorLinear_inner (I := I) (E := E) (F := F))

-- @node: scalarLpTensor
/-- For [an index set I](hyp:I) and [a complex inner product space F](hyp:F),
[the scalar tensor realization](goal) is the complex linear isometry from
the algebraic tensor product of square-summable complex families with F
into square-summable F-valued families, sending a pure tensor of v and w
to the family whose i-th entry is v at i times w. -/
noncomputable def scalarLpTensor :
    TensorProduct ℂ (lp (fun _ : I => ℂ) 2) F →ₗᵢ[ℂ] lp (fun _ : I => F) 2 :=
  { toLinearMap :=
      { toFun := fun x => ⟨fun i => TensorProduct.lid ℂ F
          (lpTensorIsometry (I := I) (E := ℂ) (F := F) x i), by
          apply (lp.memℓp (lpTensorIsometry (I := I) (E := ℂ) (F := F) x)).norm.mono
          intro i
          simp only [TensorProduct.norm_lid, le_refl]⟩
        map_add' := by
          intro a b
          ext i
          change TensorProduct.lid ℂ F (lpTensorIsometry (I := I) (E := ℂ) (F := F) (a + b) i) = _
          simp only [map_add, lp.coeFn_add]
          exact map_add (TensorProduct.lid ℂ F) _ _
        map_smul' := by intros; ext i; simp }
    norm_map' := by
      intro x
      rw [← (lpTensorIsometry (I := I) (E := ℂ) (F := F)).norm_map x]
      apply le_antisymm
      · apply lp.norm_mono (by norm_num)
        intro i
        exact (TensorProduct.norm_lid _).le
      · apply lp.norm_mono (by norm_num)
        intro i
        exact (TensorProduct.norm_lid _).ge }

-- @node: scalarLpTensor_tmul
/-- For [a square-summable family v of complex scalars](hyp:v),
[the scalar tensor realization of the pure tensor of v and w has at coordinate i the scalar v at i times w](goal). -/
@[simp] lemma scalarLpTensor_tmul (v : lp (fun _ : I => ℂ) 2) (w : F) (i : I) :
    scalarLpTensor (v ⊗ₜ[ℂ] w) i = v i • w := rfl

-- @node: scalarLpTensor_denseRange
/-- [The scalar tensor realization has dense range in the space of square-summable vector-valued families](goal). -/
lemma scalarLpTensor_denseRange :
    DenseRange (scalarLpTensor (I := I) (F := F)) := by
  classical
  let M := (scalarLpTensor (I := I) (F := F)).toLinearMap.range
  have hs (i : I) (w : F) : lp.single 2 i w ∈ M := by
    refine ⟨lp.single 2 i 1 ⊗ₜ[ℂ] w, ?_⟩
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [scalarLpTensor_tmul, lp.single_apply, hj]
  intro v
  change v ∈ closure (M : Set _)
  have hc := M.isClosed_topologicalClosure
  apply hc.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) v)
  apply Filter.Eventually.of_forall
  intro s
  exact M.topologicalClosure.sum_mem (fun i _ => M.le_topologicalClosure (hs i (v i)))

open scoped BigOperators

-- @node: norm_sum_shiftOp_le
/-- [The operator norm of any finite sum of left shifts on square-summable F-valued functions is at most the norm of the corresponding sum of left regular operators on square-summable complex functions](goal). -/
lemma norm_sum_shiftOp_le {m : ℕ} (g : Fin m → FG) :
    ‖∑ i, (shiftOp (J := F) (g i))‖ ≤ ‖∑ i, (leftReg (g i) : Op KSp)‖ := by
  classical
  let A : Op KSp := ∑ i, (leftReg (g i) : Op KSp)
  let B : Op (lp (fun _ : FG => F) 2) := ∑ i, shiftOp (g i)
  let e := scalarLpTensor (I := FG) (F := F)
  have he (x : TensorProduct ℂ KSp F) :
      B (e x) = e (A.rTensor F x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      ext y
      change (∑ i, shiftOp (g i)) (scalarLpTensor (v ⊗ₜ[ℂ] w)) y =
        scalarLpTensor ((A v) ⊗ₜ[ℂ] w) y
      simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply, scalarLpTensor_tmul]
      change (∑ i, scalarLpTensor (v ⊗ₜ[ℂ] w) ((g i)⁻¹ * y)) = (A v) y • w
      simp only [scalarLpTensor_tmul, A, sum_apply, lp.coeFn_sum,
        Finset.sum_apply, Finset.sum_smul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  apply B.opNorm_le_bound (norm_nonneg A)
  apply isClosed_property (scalarLpTensor_denseRange (I := FG) (F := F))
    (isClosed_le (by fun_prop) (by fun_prop))
  intro x
  rw [he, e.norm_map, e.norm_map]
  exact ((A.rTensor F).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_rTensor_le F A) (norm_nonneg x))

-- @node: norm_sum_shift_twist_le
/-- If [every operator in the representation σ has norm at most one](hyp:hσ),
then [the norm of a finite sum of left shifts, each composed with the constant coordinate action of σ at the corresponding group element, is at most the norm of the corresponding sum of left regular operators on square-summable complex functions](goal). -/
lemma norm_sum_shift_twist_le (σ : FG →* Op F) (hσ : ∀ g, ‖σ g‖ ≤ 1)
    {m : ℕ} (g : Fin m → FG) :
    ‖∑ i, shiftOp (g i) * diagOp (fun _ : FG => σ (g i)) 1 (fun _ => hσ _)‖ ≤
      ‖∑ i, (leftReg (g i) : Op KSp)‖ := by
  classical
  let A : Op (lp (fun _ : FG => F) 2) := diagOp (fun x => σ x) 1 hσ
  let B : Op (lp (fun _ : FG => F) 2) :=
    diagOp (fun x => σ x⁻¹) 1 (fun x => hσ x⁻¹)
  have hA : ‖A‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hB : ‖B‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hBA : B * A = 1 := by
    ext v x
    change (σ x⁻¹ * σ x) (v x) = v x
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have he (h : FG) :
      A * shiftOp h * B =
        shiftOp h * diagOp (fun _ : FG => σ h) 1 (fun _ => hσ h) := by
    ext v x
    change (σ x * σ (h⁻¹ * x)⁻¹) (v (h⁻¹ * x)) = σ h (v (h⁻¹ * x))
    rw [← map_mul]
    simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]
  calc
    _ = ‖A * (∑ i, shiftOp (g i)) * B‖ := by
      simp only [Finset.mul_sum, Finset.sum_mul, he]
    _ = ‖∑ i, shiftOp (J := F) (g i)‖ :=
      norm_conjugate_contractions A B _ hA hB hBA
    _ ≤ _ := norm_sum_shiftOp_le g

end Papers.OaiCloseSeparableCstar
