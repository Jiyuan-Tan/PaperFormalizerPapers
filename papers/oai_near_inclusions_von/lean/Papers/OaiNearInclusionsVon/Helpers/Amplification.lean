module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.Normed.Operator.Extend

/-! Concrete Hilbert-space amplification and index translations on ℓ². -/

@[expose] public section

set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon


open scoped ENNReal

variable {I E : Type*} [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open scoped TensorProduct

/-- For [an index set](hyp:I) and [a complex Hilbert space](hyp:E), the
[elementary-tensor map](goal) sends a scalar square-summable sequence and a vector
to the vector-valued sequence obtained by multiplying that vector by each coordinate. -/
-- @node: lpTensorPure
noncomputable def lpTensorPure :
    lp (fun _ : I => ℂ) 2 →ₗ[ℂ] E →ₗ[ℂ] lp (fun _ : I => E) 2 where
  toFun x :=
    { toFun := fun v => lp.mapCLM 2
        (fun _ : I => (ContinuousLinearMap.id ℂ ℂ).smulRight v)
        (norm_nonneg _) (fun _ => le_rfl) x
      map_add' := by intros; ext i; simp
      map_smul' := by intros; ext i; simp [smul_smul, mul_comm] }
  map_add' := by intros; ext v i; simp
  map_smul' := by intros; ext v i; simp [smul_smul]

omit [DecidableEq I] [CompleteSpace E] in
/-- For [a scalar square-summable sequence](hyp:x), [a vector](hyp:v), and
[an index](hyp:i), [the corresponding coordinate of their elementary tensor is
the scalar coordinate times the vector](goal). -/
-- @node: lpTensorPure_apply
lemma lpTensorPure_apply (x : lp (fun _ : I => ℂ) 2) (v : E) (i : I) :
    lpTensorPure x v i = x i • v := rfl

/-- For [an index set](hyp:I) and [a complex Hilbert space](hyp:E), the
[linear tensor map](goal) sends the algebraic tensor product of scalar square-summable
sequences with the Hilbert space to vector-valued square-summable sequences,
by sending each elementary tensor to coordinatewise scalar multiplication. -/
-- @node: lpTensorMap
noncomputable def lpTensorMap :
    (lp (fun _ : I => ℂ) 2 ⊗[ℂ] E) →ₗ[ℂ] lp (fun _ : I => E) 2 :=
  TensorProduct.lift lpTensorPure

omit [DecidableEq I] [CompleteSpace E] in
/-- For [a scalar square-summable sequence](hyp:x), [a vector](hyp:v), and
[an index](hyp:i), [the tensor map sends their elementary tensor to a sequence
whose coordinate at that index is the scalar coordinate times the vector](goal). -/
-- @node: lpTensorMap_tmul
lemma lpTensorMap_tmul (x : lp (fun _ : I => ℂ) 2) (v : E) (i : I) :
    lpTensorMap (x ⊗ₜ[ℂ] v) i = x i • v := rfl

omit [DecidableEq I] [CompleteSpace E] in
/-- For [two elements of the algebraic tensor product](hyp:x,y),
[the inner product of their images under the tensor map equals their original
inner product](goal). -/
-- @node: lpTensorMap_inner
lemma lpTensorMap_inner (x y : lp (fun _ : I => ℂ) 2 ⊗[ℂ] E) :
    inner ℂ (lpTensorMap x) (lpTensorMap y) = inner ℂ x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      simp only [lp.inner_eq_tsum, lpTensorMap_tmul, inner_smul_left,
        inner_smul_right, TensorProduct.inner_tmul, RCLike.inner_apply]
      rw [← tsum_mul_right]
      congr 1
      funext i
      ring
    | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
  | add x y hx hy => simp only [map_add, inner_add_left, hx, hy]

/-- For [an index set](hyp:I) and [a complex Hilbert space](hyp:E), the
[linear tensor isometry](goal) embeds the algebraic tensor product of scalar
square-summable sequences with the Hilbert space into vector-valued square-summable
sequences, preserving norms. -/
-- @node: lpTensorIsometry
noncomputable def lpTensorIsometry :
    (lp (fun _ : I => ℂ) 2 ⊗[ℂ] E) →ₗᵢ[ℂ] lp (fun _ : I => E) 2 :=
  lpTensorMap.isometryOfInner lpTensorMap_inner

omit [DecidableEq I] [CompleteSpace E] in
/-- [The tensor map has dense range in the space of vector-valued square-summable
sequences](goal). -/
-- @node: lpTensorMap_denseRange
lemma lpTensorMap_denseRange : DenseRange (lpTensorMap (I := I) (E := E)) := by
  classical
  intro x
  apply (LinearMap.range (lpTensorMap (I := I) (E := E))).isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single (by norm_num) x)
  apply Filter.Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i hi
  apply subset_closure
  refine ⟨lp.single 2 i 1 ⊗ₜ[ℂ] x i, ?_⟩
  ext j
  by_cases h : i = j <;> simp [lpTensorMap_tmul, lp.single_apply, h]

set_option maxHeartbeats 800000 in
-- Elaborating the extension through the tensor isometry requires a larger reduction budget.
/-- For [a bounded linear operator on scalar square-summable sequences](hyp:X),
[there exists a bounded linear operator on vector-valued square-summable sequences
whose response at any coordinate to a vector supported at a single index is the
corresponding scalar matrix entry times that vector, and whose operator norm is
at most that of the scalar operator](goal). -/
-- @node: amplification_exists
lemma amplification_exists (X : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    ∃ T : lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2,
      (∀ i j v, T (lp.single 2 j v) i = (X (lp.single 2 j 1) i) • v) ∧ ‖T‖ ≤ ‖X‖ := by
  let e := lpTensorIsometry (I := I) (E := E)
  let f := e.toLinearMap.comp (X.rTensor E).toLinearMap
  have hdense : DenseRange e.toLinearMap := lpTensorMap_denseRange
  have hbound : ∀ x, ‖f x‖ ≤ ‖X‖ * ‖e.toLinearMap x‖ := by
    intro x
    change ‖e (X.rTensor E x)‖ ≤ ‖X‖ * ‖e x‖
    rw [e.norm_map, e.norm_map]
    exact (X.rTensor E).le_of_opNorm_le (X.norm_rTensor_le E) x
  refine ⟨f.extendOfNorm e.toLinearMap, ?_,
    LinearMap.opNorm_extendOfNorm_le hdense (norm_nonneg X) hbound⟩
  intro i j v
  have hsingle : e.toLinearMap (lp.single 2 j 1 ⊗ₜ[ℂ] v) = lp.single 2 j v := by
    ext k
    by_cases h : j = k <;>
      simp [e, lpTensorIsometry, lpTensorMap_tmul, lp.single_apply, h]
  rw [← hsingle, LinearMap.extendOfNorm_eq hdense ⟨‖X‖, hbound⟩]
  exact lpTensorMap_tmul (X (lp.single 2 j 1)) v i

/-- For [an index set](hyp:I), [a complex Hilbert space](hyp:E), and
[a bounded linear operator on scalar square-summable sequences](hyp:X), the
[amplification](goal) is a chosen bounded linear operator on vector-valued
square-summable sequences with the same scalar matrix entries acting on each vector
and with operator norm no greater than the original operator's. -/
noncomputable def amplify (X : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2 :=
  Classical.choose (amplification_exists (E := E) X)

/-- For [a bounded linear operator on scalar square-summable sequences](hyp:X),
[its amplification sends a vector supported at a single index to the sequence
given by the corresponding scalar matrix column times that vector, and has
operator norm at most the original operator's norm](goal). -/
-- @node: amplify_spec
lemma amplify_spec (X : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) :
    (∀ i j v, amplify (E := E) X (lp.single 2 j v) i =
      (X (lp.single 2 j 1) i) • v) ∧ ‖amplify (E := E) X‖ ≤ ‖X‖ := by
  exact Classical.choose_spec (amplification_exists (E := E) X)

omit [DecidableEq I] in
/-- For [an index set](hyp:I), [a complex Hilbert space](hyp:E), and
[a bijection of the index set with itself](hyp:e), the [reindexing isometry](goal)
replaces each coordinate of a vector-valued square-summable sequence by its
coordinate at the image of that index under the bijection. -/
-- @node: lpReindexIsometry
noncomputable def lpReindexIsometry (e : I ≃ I) :
    lp (fun _ : I => E) 2 →ₗᵢ[ℂ] lp (fun _ : I => E) 2 where
  toFun ξ := ⟨fun i => ξ (e i), memℓp_gen
    ((e.summable_iff).2 ((lp.memℓp ξ).summable (by norm_num)))⟩
  map_add' ξ η := by ext i; rfl
  map_smul' c ξ := by ext i; rfl
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.tsum_eq (fun i => ‖ξ i‖ ^ (2 : ℝ≥0∞).toReal)

omit [DecidableEq I] in
/-- For [a bijection of the index set with itself](hyp:e), [there exists a bounded
linear operator on vector-valued square-summable sequences that replaces each
coordinate by the coordinate at its image under the bijection and has operator
norm at most one](goal). -/
-- @node: lpReindex_exists
lemma lpReindex_exists (e : I ≃ I) :
    ∃ T : lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2,
      (∀ ξ i, T ξ i = ξ (e i)) ∧ ‖T‖ ≤ 1 := by
  exact ⟨(lpReindexIsometry (E := E) e).toContinuousLinearMap,
    fun _ _ => rfl, (lpReindexIsometry (E := E) e).norm_toContinuousLinearMap_le⟩

omit [DecidableEq I] in
/-- For [an index set](hyp:I), [a complex Hilbert space](hyp:E), and
[a bijection of the index set with itself](hyp:e), the [reindexing operator](goal)
is a chosen bounded linear operator that pulls back vector-valued square-summable
sequences along the bijection, with operator norm at most one. -/
noncomputable def lpReindex (e : I ≃ I) :
    lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2 :=
  Classical.choose (lpReindex_exists (E := E) e)

omit [DecidableEq I] in
/-- For [a bijection of the index set](hyp:e), [a vector-valued square-summable
sequence](hyp:ξ), and [an index](hyp:i), [the reindexed sequence at that index
equals the original sequence at the image of the index under the bijection](goal). -/
-- @node: lpReindex_apply
lemma lpReindex_apply (e : I ≃ I) (ξ : lp (fun _ : I => E) 2) (i : I) :
    lpReindex e ξ i = ξ (e i) :=
  (Classical.choose_spec (lpReindex_exists (E := E) e)).1 ξ i

omit [DecidableEq I] in
/-- For [a bijection of the index set](hyp:e), [the chosen reindexing operator
equals the bounded linear operator associated with the reindexing isometry](goal). -/
-- @node: lpReindex_eq_isometry
lemma lpReindex_eq_isometry (e : I ≃ I) :
    lpReindex (E := E) e = (lpReindexIsometry (E := E) e).toContinuousLinearMap := by
  ext ξ i
  exact lpReindex_apply e ξ i

omit [DecidableEq I] in
/-- For [a bijection of the index set](hyp:e), [the reindexing operator on
vector-valued square-summable sequences is unitary](goal). -/
-- @node: lpReindex_mem_unitary
lemma lpReindex_mem_unitary (e : I ≃ I) :
    lpReindex (E := E) e ∈ unitary (lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2) := by
  let f := lpReindexIsometry (E := E) e
  have hsurj : Function.Surjective f := by
    intro ξ
    refine ⟨lpReindexIsometry (E := E) e.symm ξ, ?_⟩
    ext i
    exact congrArg ξ (e.symm_apply_apply i)
  rw [lpReindex_eq_isometry]
  exact (Unitary.linearIsometryEquiv.symm
    (LinearIsometryEquiv.ofSurjective f hsurj)).property

omit [DecidableEq I] in
/-- For [a bijection of the index set](hyp:e), [the adjoint of its reindexing
operator is the reindexing operator for the inverse bijection](goal). -/
-- @node: lpReindex_star
lemma lpReindex_star (e : I ≃ I) :
    star (lpReindex (E := E) e) = lpReindex (E := E) e.symm := by
  have hinv : lpReindex (E := E) e * lpReindex (E := E) e.symm = 1 := by
    ext ξ i
    simp only [mul_apply_eq_comp, lpReindex_apply,
      Equiv.symm_apply_apply, one_apply_eq_self]
  calc
    star (lpReindex (E := E) e) =
        star (lpReindex (E := E) e) * (lpReindex (E := E) e * lpReindex e.symm) := by
      rw [hinv, mul_one]
    _ = lpReindex e.symm := by
      rw [← mul_assoc, Unitary.star_mul_self_of_mem (lpReindex_mem_unitary (E := E) e), one_mul]

end Papers.OaiNearInclusionsVon
