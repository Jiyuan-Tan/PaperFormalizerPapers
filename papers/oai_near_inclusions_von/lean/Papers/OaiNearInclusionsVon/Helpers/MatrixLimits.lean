module

public import Papers.OaiNearInclusionsVon.Helpers.LaurentUnitary
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-! Weak operator limits for finite-dimensional Laurent substitution. -/

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace Papers.OaiNearInclusionsVon

open Filter
open scoped Topology

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

/-- For [a sequence of bounded linear operators T](hyp:T), [a bounded linear operator R](hyp:R),
[a real bound C](hyp:C), and [a fixed test vector ξ](hyp:ξ), if
[every operator in T has norm at most C](hyp:hC), then
[the vectors η for which the inner products of ξ with T applied to η converge to the inner
product of ξ with R applied to η form a closed set](goal). -/
-- @node: bounded_wot_test_isClosed
lemma bounded_wot_test_isClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : ℕ → E →L[ℂ] E) (R : E →L[ℂ] E) (C : ℝ)
    (hC : ∀ j, ‖T j‖ ≤ C) (ξ : E) :
    IsClosed {η | Tendsto (fun j => inner ℂ ξ (T j η)) atTop
      (𝓝 (inner ℂ ξ (R η)))} := by
  have hequi : Equicontinuous (fun j η => inner ℂ ξ (T j η)) := by
    apply Metric.equicontinuous_of_continuity_modulus
      (fun d : ℝ => (‖ξ‖ * C) * d) (by simpa using
        (tendsto_const_nhds.mul (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0))))
    intro x y j
    exact (((innerSL ℂ ξ).comp (T j)).dist_le_opNorm x y).trans
      (mul_le_mul_of_nonneg_right
        (((innerSL ℂ ξ).opNorm_comp_le (T j)).trans (by
          rw [innerSL_apply_norm]
          exact mul_le_mul_of_nonneg_left (hC j) (norm_nonneg ξ))) dist_nonneg)
  exact hequi.isClosed_setOfPred_tendsto ((innerSL ℂ ξ).comp R).continuous

/-- Given [a linear subspace M of the space of square-summable vector-valued sequences](hyp:M),
if [M is closed](hyp:hM) and [M contains every sequence supported at a single index](hyp:hsingle),
then [any square-summable sequence η](hyp:η) [belongs to M](goal). -/
-- @node: lp_mem_closed_submodule
lemma lp_mem_closed_submodule {I E : Type*} [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Submodule ℂ (lp (fun _ : I => E) 2)) (hM : IsClosed (M : Set (lp (fun _ : I => E) 2)))
    (hsingle : ∀ i v, lp.single 2 i v ∈ M) (η : lp (fun _ : I => E) 2) : η ∈ M := by
  apply hM.mem_of_tendsto (lp.hasSum_single (by norm_num) η)
  exact Eventually.of_forall fun s => M.sum_mem fun i _ => hsingle i (η i)

/-- For [an operator U on a finite-dimensional Hilbert space](hyp:U) that
[is unitary](hyp:hU), let [M be a linear subspace of the nested square-summable space L](hyp:M).
If [M is closed](hyp:hM) and [M contains every vector supported at one pair of indices whose
nonzero entry is an eigenvector of U with eigenvalue on the unit circle](hyp:h), then
[every vector η in L](hyp:η) [belongs to M](goal). -/
-- @node: lsp_mem_closed_submodule_of_eigen
lemma lsp_mem_closed_submodule_of_eigen [FiniteDimensional ℂ D]
    (U : D →L[ℂ] D) (hU : U ∈ unitary _)
    (M : Submodule ℂ (Lsp D)) (hM : IsClosed (M : Set (Lsp D)))
    (h : ∀ (z : Circle) (v : D), U v = (z : ℂ) • v → ∀ i j,
      lp.single 2 i (lp.single 2 j v) ∈ M) (η : Lsp D) : η ∈ M := by
  apply lp_mem_closed_submodule M hM
  intro i y
  let S := lp.singleContinuousLinearMap ℂ (fun _ : FreeGrp => lp (fun _ : FreeGrp => D) 2) 2 i
  let N := M.comap S.toLinearMap
  have hN : IsClosed (N : Set (lp (fun _ : FreeGrp => D) 2)) := hM.preimage S.continuous
  change y ∈ N
  apply lp_mem_closed_submodule N hN
  intro j v
  have hv : v ∈ ⨆ z : Circle, Module.End.eigenspace U.toLinearMap (z : ℂ) := by
    rw [unitary_iSup_circle_eigenspace_eq_top U hU]
    trivial
  exact Submodule.iSup_induction (motive := fun v => lp.single 2 j v ∈ N) _ hv
    (fun z v hv => h z v (Module.End.mem_eigenspace_iff.mp hv) i j)
    (by simp only [lp.single_zero]; exact N.zero_mem)
    (fun x y hx hy => by rw [lp.single_add]; exact N.add_mem hx hy)

/-- For [an operator U](hyp:U), [a unit-circle scalar z](hyp:z), and [a vector v](hyp:v)
such that [U sends v to z times v](hyp:hv), and for [tree-space vectors x and y](hyp:x,y),
[the first matrix limit sends the elementary tensor x ⊗ y ⊗ v to the tensor obtained by
applying t times z times the distinguished projection to x](goal). -/
-- @node: matrixLimitA_tensorRight_eigen
lemma matrixLimitA_tensorRight_eigen (U : D →L[ℂ] D)
    (z : Circle) (v : D) (hv : U v = (z : ℂ) • v) (x y : TreeSpace) :
    matrixLimitA U (lpTensorRight (lpTensorRight v y) x) =
      lpTensorRight (lpTensorRight v y) ((((tParam : ℂ) * (z : ℂ)) • projE) x) := by
  rw [matrixLimitA, smul_apply, mul_apply_eq_comp, ampD_tensorRight, hv,
    ampFst, amplify_tensorRight]
  ext i j
  simp only [lpTensorRight_apply, lp.coeFn_smul, Pi.smul_apply, smul_apply, smul_smul,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, smul_eq_mul]
  congr 1
  change (tParam : ℂ) * (projE x i) * (y j * (z : ℂ)) =
    (tParam : ℂ) * (z : ℂ) * (projE x i) * y j
  ring

/-- For [an operator U](hyp:U), [a unit-circle scalar z](hyp:z), and [a vector v](hyp:v)
such that [U sends v to z times v](hyp:hv), and for [tree-space vectors x and y](hyp:x,y),
[the second matrix limit sends the elementary tensor x ⊗ y ⊗ v to the tensor obtained by
applying t times z times the distinguished projection to y](goal). -/
-- @node: matrixLimitB_tensorRight_eigen
lemma matrixLimitB_tensorRight_eigen (U : D →L[ℂ] D)
    (z : Circle) (v : D) (hv : U v = (z : ℂ) • v) (x y : TreeSpace) :
    matrixLimitB U (lpTensorRight (lpTensorRight v y) x) =
      lpTensorRight (lpTensorRight v ((((tParam : ℂ) * (z : ℂ)) • projE) y)) x := by
  rw [matrixLimitB, smul_apply, mul_apply_eq_comp, ampD_tensorRight, hv,
    ampSnd_tensorRight]
  ext i j
  simp only [lpTensorRight_apply, lp.coeFn_smul, Pi.smul_apply, smul_apply, smul_smul,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, smul_eq_mul]
  congr 1
  change (tParam : ℂ) * x i * (projE y j * (z : ℂ)) =
    x i * ((tParam : ℂ) * (z : ℂ) * projE y j)
  ring

/-- Given [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), and [operators U and V](hyp:U,V)
that [are unitary on a nonzero finite-dimensional space](hyp:hUV), suppose
[both substituted Laurent series converge absolutely at every group element](hyp:habs).
For [test vectors ξ and η in L](hyp:ξ,η), [the inner products of ξ with the first substituted
representation at successive free generators applied to η converge to the inner product
of ξ with the first matrix limit applied to η](goal). -/
-- @node: matrixRepA_gen_tendsto_wot
lemma matrixRepA_gen_tendsto_wot (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (U V : D →L[ℂ] D) (hUV : NearUnitaryPair U V)
    (habs : MatrixRepsAbsConv A U V) (ξ η : Lsp D) :
    Tendsto (fun j => inner ℂ ξ (matrixRepA A U (gen j) η)) atTop
      (𝓝 (inner ℂ ξ (matrixLimitA U η))) := by
  letI : FiniteDimensional ℂ D := hUV.2.1
  let M : Submodule ℂ (Lsp D) :=
    { carrier := {η | Tendsto (fun j => inner ℂ ξ (matrixRepA A U (gen j) η)) atTop
        (𝓝 (inner ℂ ξ (matrixLimitA U η)))}
      zero_mem' := by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
      add_mem' := fun hx hy => by simpa only [Set.mem_ofPred_eq, map_add, inner_add_right] using hx.add hy
      smul_mem' := fun c x hx => by simpa only [Set.mem_ofPred_eq, map_smul, inner_smul_right] using hx.const_mul c }
  apply lsp_mem_closed_submodule_of_eigen U hUV.2.2.1 M
    (bounded_wot_test_isClosed _ _ S0 (fun j => matrixRepA_norm_le π A hπ U hUV.2.2.1 (gen j)) ξ)
    ?_ η
  intro z v hv i j
  let F : TreeSpace →L[ℂ] Lsp D := lpTensorRight (lpTensorRight v (treeBasis j))
  have ht := hπ.2.2.1 z (F.adjoint ξ) (treeBasis i)
  simp only [ContinuousLinearMap.adjoint_inner_left] at ht
  change Tendsto (fun n => inner ℂ ξ (matrixRepA A U (gen n)
    (lp.single 2 i (lp.single 2 j v)))) atTop
    (𝓝 (inner ℂ ξ (matrixLimitA U (lp.single 2 i (lp.single 2 j v)))))
  have heq (g : FreeGrp) := matrixRepA_tensorRight_eigen π A hπ U hUV.2.2.1
    z v hv g (treeBasis i) (treeBasis j)
  have hlim := matrixLimitA_tensorRight_eigen U z v hv (treeBasis i) (treeBasis j)
  simp only [treeBasis, lpTensorRight_single] at heq hlim
  simpa only [heq, hlim, F, treeBasis, lpTensorRight_single] using ht

/-- Given [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), and [operators U and V](hyp:U,V)
that [are unitary on a nonzero finite-dimensional space](hyp:hUV), suppose
[both substituted Laurent series converge absolutely at every group element](hyp:habs).
For [test vectors ξ and η in L](hyp:ξ,η), [the inner products of ξ with the second substituted
representation at successive free generators applied to η converge to the inner product
of ξ with the second matrix limit applied to η](goal). -/
-- @node: matrixRepB_gen_tendsto_wot
lemma matrixRepB_gen_tendsto_wot (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (U V : D →L[ℂ] D) (hUV : NearUnitaryPair U V)
    (habs : MatrixRepsAbsConv A U V) (ξ η : Lsp D) :
    Tendsto (fun j => inner ℂ ξ (matrixRepB A V (gen j) η)) atTop
      (𝓝 (inner ℂ ξ (matrixLimitB V η))) := by
  letI : FiniteDimensional ℂ D := hUV.2.1
  let M : Submodule ℂ (Lsp D) :=
    { carrier := {η | Tendsto (fun j => inner ℂ ξ (matrixRepB A V (gen j) η)) atTop
        (𝓝 (inner ℂ ξ (matrixLimitB V η)))}
      zero_mem' := by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
      add_mem' := fun hx hy => by simpa only [Set.mem_ofPred_eq, map_add, inner_add_right] using hx.add hy
      smul_mem' := fun c x hx => by simpa only [Set.mem_ofPred_eq, map_smul, inner_smul_right] using hx.const_mul c }
  apply lsp_mem_closed_submodule_of_eigen V hUV.2.2.2 M
    (bounded_wot_test_isClosed _ _ S0 (fun j => matrixRepB_norm_le π A hπ V hUV.2.2.2 (gen j)) ξ)
    ?_ η
  intro z v hv i j
  let F := (lp.singleContinuousLinearMap ℂ
    (fun _ : FreeGrp => lp (fun _ : FreeGrp => D) 2) 2 i).comp (lpTensorRight v)
  have ht := hπ.2.2.1 z (F.adjoint ξ) (treeBasis j)
  simp only [ContinuousLinearMap.adjoint_inner_left] at ht
  change Tendsto (fun n => inner ℂ ξ (lp.single 2 i
    (lpTensorRight v ((π z (gen n) : TreeSpace →L[ℂ] TreeSpace) (treeBasis j))))) atTop
    (𝓝 (inner ℂ ξ (lp.single 2 i
      (lpTensorRight v ((((tParam : ℂ) * (z : ℂ)) • projE) (treeBasis j)))))) at ht
  change Tendsto (fun n => inner ℂ ξ (matrixRepB A V (gen n)
    (lp.single 2 i (lp.single 2 j v)))) atTop
    (𝓝 (inner ℂ ξ (matrixLimitB V (lp.single 2 i (lp.single 2 j v)))))
  have heq (g : FreeGrp) := matrixRepB_tensorRight_eigen π A hπ V hUV.2.2.2
    z v hv g (treeBasis i) (treeBasis j)
  have hlim := matrixLimitB_tensorRight_eigen V z v hv (treeBasis i) (treeBasis j)
  simp only [treeBasis, lpTensorRight_single] at heq hlim
  simpa only [heq, hlim, treeBasis] using ht

/-- Given [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), and [operators U and V](hyp:U,V)
that [are unitary on a nonzero finite-dimensional space](hyp:hUV), for
[test vectors ξ and η in L](hyp:ξ,η), [the inner products of ξ with the first substituted
representation at successive free generators applied to η converge to the inner product
of ξ with the first matrix limit applied to η](goal).

This is the first convergence in `eq:matrix-limits`; absolute convergence follows from
the circle family and the input unitaries. -/
lemma matrixLimitA_tendsto_wot (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (U V : D →L[ℂ] D) (hUV : NearUnitaryPair U V)
    (ξ η : Lsp D) :
    Tendsto (fun j => inner ℂ ξ (matrixRepA A U (gen j) η)) atTop
      (𝓝 (inner ℂ ξ (matrixLimitA U η))) := by
  exact matrixRepA_gen_tendsto_wot π A hπ U V hUV
    (matrixRepsAbsConv_of_circleFamily π A hπ U V hUV.2.2.1 hUV.2.2.2) ξ η

/-- Given [a circle-indexed representation family π](hyp:π) and [Laurent coefficients A](hyp:A)
that [satisfy the circle-family assumptions](hyp:hπ), and [operators U and V](hyp:U,V)
that [are unitary on a nonzero finite-dimensional space](hyp:hUV), for
[test vectors ξ and η in L](hyp:ξ,η), [the inner products of ξ with the second substituted
representation at successive free generators applied to η converge to the inner product
of ξ with the second matrix limit applied to η](goal).

This is the second convergence in `eq:matrix-limits`; absolute convergence follows from
the circle family and the input unitaries. -/
lemma matrixLimitB_tendsto_wot (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (U V : D →L[ℂ] D) (hUV : NearUnitaryPair U V)
    (ξ η : Lsp D) :
    Tendsto (fun j => inner ℂ ξ (matrixRepB A V (gen j) η)) atTop
      (𝓝 (inner ℂ ξ (matrixLimitB V η))) := by
  exact matrixRepB_gen_tendsto_wot π A hπ U V hUV
    (matrixRepsAbsConv_of_circleFamily π A hπ U V hUV.2.2.1 hUV.2.2.2) ξ η

set_option linter.defProp false in
/-- For [a Hilbert space D](hyp:D), [a circle-indexed representation family π](hyp:π),
[Laurent coefficients A](hyp:A) that [satisfy the circle-family assumptions](hyp:hπ), and
[operators U and V on D](hyp:U,V) that [are unitary with D nonzero and finite-dimensional](hyp:hUV),
[the paired weak operator limits](goal) consist of
[convergence of the first substituted representation at successive free generators to the
first matrix limit, tested against every pair of vectors](step:1), and
[convergence of the second substituted representation at successive free generators to the
second matrix limit, tested against every pair of vectors](step:2).

These are the two claims in `eq:matrix-limits`; absolute convergence follows from the circle
family and the input unitaries. -/
-- @node: def:matrix-limits
def matrixLimitsWot (π : CircleRep) (A : LaurentData)
    (hπ : IsCircleFamily π A) (U V : D →L[ℂ] D) (hUV : NearUnitaryPair U V) :
    (∀ ξ η : Lsp D, Tendsto (fun j => inner ℂ ξ (matrixRepA A U (gen j) η)) atTop
      (𝓝 (inner ℂ ξ (matrixLimitA U η)))) ∧
    (∀ ξ η : Lsp D, Tendsto (fun j => inner ℂ ξ (matrixRepB A V (gen j) η)) atTop
      (𝓝 (inner ℂ ξ (matrixLimitB V η)))) :=
  ⟨fun ξ η => matrixLimitA_tendsto_wot π A hπ U V hUV ξ η,
    fun ξ η => matrixLimitB_tendsto_wot π A hπ U V hUV ξ η⟩

end Papers.OaiNearInclusionsVon
