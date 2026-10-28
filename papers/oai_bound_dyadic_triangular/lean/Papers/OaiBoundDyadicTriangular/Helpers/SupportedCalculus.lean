module

public import Papers.OaiBoundDyadicTriangular.Helpers.SylvesterOrder
public import Papers.OaiBoundDyadicTriangular.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Calculus on the fixed-support symmetric matrix space

The fixed-support space is an intersection of kernels of linear maps. Its
relative topology comes from the matrix operator norm.
-/

@[expose] public section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace MatrixOrder

namespace Papers.OaiBoundDyadicTriangular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For [a real square matrix P](hyp:P), the [fixed-support symmetric space](goal)
consists of symmetric matrices that send every vector in the kernel of P to zero. -/
noncomputable def supportedTangent (P : Matrix ι ι ℝ) : Submodule ℝ (Matrix ι ι ℝ) :=
  LinearMap.ker ((Matrix.transposeLinearEquiv ι ι ℝ ℝ).toLinearMap - LinearMap.id) ⊓
    ⨅ x : LinearMap.ker (Matrix.toLin' P),
      LinearMap.ker ((Matrix.mulVecBilin ℝ ℝ).flip x.val)

-- @node: mem_supportedTangent
/-- For real square matrices P and K, [K belongs to the fixed-support symmetric
space of P if and only if K is symmetric and annihilates the kernel of P](goal). -/
lemma mem_supportedTangent (P K : Matrix ι ι ℝ) :
    K ∈ supportedTangent P ↔ HessianDirection P K := by
  simp only [supportedTangent, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker]
  change (K.transpose - K = 0 ∧
    ∀ x : LinearMap.ker (Matrix.toLin' P), K *ᵥ x.val = 0) ↔
    K.IsSymm ∧ AnnihilatesKernel P K
  rw [sub_eq_zero]
  constructor
  · rintro ⟨hSymm, hKer⟩
    exact ⟨hSymm, fun x hx => hKer ⟨x, hx⟩⟩
  · rintro ⟨hSymm, hKer⟩
    exact ⟨hSymm, fun x => hKer x.val x.property⟩

-- @node: base_mem_supportedTangent
/-- If [P is positive semidefinite](hyp:hP), then [P itself belongs to its
fixed-support symmetric space](goal). -/
lemma base_mem_supportedTangent (P : Matrix ι ι ℝ) (hP : HessianPositiveSupport P) :
    P ∈ supportedTangent P := by
  apply (mem_supportedTangent P P).mpr
  exact ⟨Matrix.isHermitian_iff_isSymm.mp hP.isHermitian, fun _ hx => hx⟩

-- @node: supportedTangent_isHermitian
/-- Every matrix Q in the fixed-support symmetric space of P
[is Hermitian, or equivalently symmetric over the real numbers](goal). -/
lemma supportedTangent_isHermitian (P : Matrix ι ι ℝ) (Q : supportedTangent P) :
    Q.val.IsHermitian := by
  exact Matrix.isHermitian_iff_isSymm.mpr ((mem_supportedTangent P Q.val).mp Q.property).1

/-- For [a real square matrix P](hyp:P), the [positive-support locus](goal) is the
set of matrices in its fixed-support symmetric space whose quadratic form is
strictly positive on every nonzero vector orthogonal to the kernel of P. -/
noncomputable def positiveSupportLocus (P : Matrix ι ι ℝ) : Set (supportedTangent P) :=
  {Q | ∀ x : supportSubspace P, x ≠ 0 →
    0 < inner ℝ x.val (Matrix.toEuclideanLin Q.val x.val)}

-- @node: base_mem_positiveSupportLocus
/-- If [P is positive semidefinite](hyp:hP), then [P belongs to its own
positive-support locus](goal): its quadratic form is strictly positive on every
nonzero vector orthogonal to its kernel. -/
lemma base_mem_positiveSupportLocus (P : Matrix ι ι ℝ) (hP : HessianPositiveSupport P) :
    (⟨P, base_mem_supportedTangent P hP⟩ : supportedTangent P) ∈
      positiveSupportLocus P := by
  intro x hx
  have hInner : inner ℝ x.val (Matrix.toEuclideanLin P x.val) =
      star (WithLp.ofLp x.val) ⬝ᵥ P *ᵥ WithLp.ofLp x.val := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
      dotProduct_comm]
  rw [hInner]
  apply lt_of_le_of_ne (hP.dotProduct_mulVec_nonneg _)
  intro he
  have hmul := (hP.dotProduct_mulVec_zero_iff (WithLp.ofLp x.val)).mp he.symm
  have hker : x.val ∈ LinearMap.ker (Matrix.toEuclideanLin P) := by
    rw [LinearMap.mem_ker, Matrix.toEuclideanLin_apply, hmul]
    rfl
  have hzero : x.val = 0 := inner_self_eq_zero.mp (x.property x.val hker)
  exact hx (Subtype.ext hzero)

-- @node: positiveSupportLocus_eq_unit
/-- For a real square matrix P, [its positive-support locus consists exactly of
the matrices in its fixed-support symmetric space whose quadratic form is
strictly positive on every unit vector orthogonal to the kernel of P](goal). -/
lemma positiveSupportLocus_eq_unit (P : Matrix ι ι ℝ) :
    positiveSupportLocus P = {Q | ∀ x : supportSubspace P, ‖x‖ = 1 →
      0 < inner ℝ x.val (Matrix.toEuclideanLin Q.val x.val)} := by
  ext Q
  constructor
  · intro h x hx
    exact h x (fun he => by simp [he] at hx)
  · intro h x hx
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hy : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hp := h ((‖x‖⁻¹ : ℝ) • x) hy
    simp only [Submodule.coe_smul, map_smul, real_inner_smul_left,
      real_inner_smul_right] at hp
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp
      ((mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp hp)

-- @node: isOpen_positiveSupportLocus
/-- For any real square matrix P, [the positive-support locus is open in its
fixed-support symmetric space](goal). -/
lemma isOpen_positiveSupportLocus (P : Matrix ι ι ℝ) :
    IsOpen (positiveSupportLocus P) := by
  let S := Metric.sphere (0 : supportSubspace P) 1
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp
    (isCompact_sphere (0 : supportSubspace P) 1)
  let A : Matrix ι ι ℝ →ₗ[ℝ] (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
  have hA : Continuous A := A.continuous_of_finiteDimensional
  have hc : Continuous (fun z : supportedTangent P × S =>
      inner ℝ z.2.val.val (Matrix.toEuclideanLin z.1.val z.2.val.val)) := by
    change Continuous (fun z : supportedTangent P × S =>
      inner ℝ z.2.val.val (A z.1.val z.2.val.val))
    fun_prop
  have hclosed : IsClosed {z : supportedTangent P × S |
      inner ℝ z.2.val.val (Matrix.toEuclideanLin z.1.val z.2.val.val) ≤ 0} :=
    isClosed_le hc continuous_const
  have ho := (isClosedMap_fst_of_compactSpace _ hclosed).isOpen_compl
  rw [positiveSupportLocus_eq_unit]
  convert ho using 1
  ext Q
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists,
    not_and, not_le]
  constructor
  · intro h z hz he
    subst Q
    exact (not_le_of_gt (h z.2.val
      (by simpa [S, Metric.mem_sphere, dist_zero_right] using z.2.property))) hz
  · intro h x hx
    apply lt_of_not_ge
    intro hle
    exact h (Q, ⟨x, by simpa [S, Metric.mem_sphere, dist_zero_right] using hx⟩) hle rfl

/-- For matrices B and X in the fixed-support symmetric space of P,
[the sum of the products BX and XB also belongs to that space](goal). -/
-- @node: jordan_mem_supportedTangent
lemma jordan_mem_supportedTangent (P : Matrix ι ι ℝ) (B X : supportedTangent P) :
    B.val * X.val + X.val * B.val ∈ supportedTangent P := by
  have hB := (mem_supportedTangent P B.val).mp B.property
  have hX := (mem_supportedTangent P X.val).mp X.property
  apply (mem_supportedTangent P _).mpr
  constructor
  · change (B.val * X.val + X.val * B.val).transpose = _
    simp only [Matrix.transpose_add, Matrix.transpose_mul, hB.1.eq, hX.1.eq]
    exact add_comm _ _
  · intro x hx
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hB.2 x hx, hX.2 x hx,
      Matrix.mulVec_zero, add_zero]

/-- For [a real square matrix P](hyp:P), the [supported Jordan product](goal)
is the bilinear map on its fixed-support symmetric space that sends B and X to
the sum of the matrix products BX and XB. -/
-- @node: supportedJordanLinear
noncomputable def supportedJordanLinear (P : Matrix ι ι ℝ) :
    supportedTangent P →ₗ[ℝ] supportedTangent P →ₗ[ℝ] supportedTangent P :=
  LinearMap.mk₂ ℝ (fun B X => ⟨B.val * X.val + X.val * B.val,
    jordan_mem_supportedTangent P B X⟩)
    (by intros; apply Subtype.ext; simp only [Submodule.coe_add, Matrix.add_mul,
      Matrix.mul_add]; abel)
    (by intros; apply Subtype.ext; simp [Matrix.smul_mul, Matrix.mul_smul, smul_add])
    (by intros; apply Subtype.ext; simp only [Submodule.coe_add, Matrix.add_mul,
      Matrix.mul_add]; abel)
    (by intros; apply Subtype.ext; simp [Matrix.smul_mul, Matrix.mul_smul, smul_add])

/-- For [a real square matrix P](hyp:P), the [continuous supported Jordan
product](goal) is formed by [taking the fixed-support symmetric space of P](step:1),
[identifying its linear operators with continuous linear operators](step:2), and
[regarding the bilinear map sending B and X to the sum of BX and XB as continuous
in both arguments](step:3). -/
-- @node: supportedJordan
noncomputable def supportedJordan (P : Matrix ι ι ℝ) :
    supportedTangent P →L[ℝ] supportedTangent P →L[ℝ] supportedTangent P :=
  let E := supportedTangent P
  let C : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E) := LinearMap.toContinuousLinearMap
  (C.toLinearMap.comp (supportedJordanLinear P)).toContinuousLinearMap

-- @node: supportedJordan_apply
/-- For matrices B and X in the fixed-support symmetric space of P,
[their continuous supported Jordan product is the sum of the ordinary matrix
products BX and XB](goal). -/
lemma supportedJordan_apply (P : Matrix ι ι ℝ) (B X : supportedTangent P) :
    (supportedJordan P B X).val = B.val * X.val + X.val * B.val := rfl

/-- For [a real square matrix P](hyp:P) and [a matrix B in its fixed-support
symmetric space](hyp:B), the [supported square of B](goal) is half the supported
Jordan product of B with itself, giving the ordinary matrix square within that space. -/
-- @node: supportedSquare
noncomputable def supportedSquare (P : Matrix ι ι ℝ) (B : supportedTangent P) :
    supportedTangent P := (1 / 2 : ℝ) • supportedJordan P B B

-- @node: supportedSquare_apply
/-- For a matrix B in the fixed-support symmetric space of P,
[its supported square equals the ordinary matrix product of B with itself](goal). -/
lemma supportedSquare_apply (P : Matrix ι ι ℝ) (B : supportedTangent P) :
    (supportedSquare P B).val = B.val * B.val := by
  change (1 / 2 : ℝ) • (B.val * B.val + B.val * B.val) = _
  rw [← two_smul ℝ, smul_smul]
  norm_num

/-- For any real square matrix P, [squaring is infinitely differentiable on its
fixed-support symmetric space](goal). -/
@[fun_prop]
-- @node: contDiff_supportedSquare
lemma contDiff_supportedSquare (P : Matrix ι ι ℝ) :
    ContDiff ℝ ⊤ (supportedSquare P) := by
  unfold supportedSquare
  fun_prop

/-- For a matrix B in the fixed-support symmetric space of P,
[the derivative of squaring at B sends a direction X to the sum of BX and XB](goal). -/
-- @node: hasFDerivAt_supportedSquare
lemma hasFDerivAt_supportedSquare (P : Matrix ι ι ℝ) (B : supportedTangent P) :
    HasFDerivAt (supportedSquare P) (supportedJordan P B) B := by
  have h := ((supportedJordan P).hasFDerivAt_of_bilinear
    (hasFDerivAt_id B) (hasFDerivAt_id B)).const_smul (1 / 2 : ℝ)
  convert h using 1 <;> try rfl
  ext X : 1
  apply Subtype.ext
  simp [supportedJordan_apply, smul_add]
  module

/-- If [P is positive semidefinite](hyp:hP), then [the map sending a matrix X in
the fixed-support symmetric space of P to the sum of the products of the positive
square root of P with X in the two possible orders is injective](goal). -/
-- @node: sqrt_sylvester_supported_injective
lemma sqrt_sylvester_supported_injective (P : Matrix ι ι ℝ) (hP : P.PosSemidef) :
    Function.Injective (fun X : supportedTangent P =>
      CFC.sqrt P * X.val + X.val * CFC.sqrt P) := by
  suffices hz : ∀ X : supportedTangent P,
      CFC.sqrt P * X.val + X.val * CFC.sqrt P = 0 → X = 0 by
    intro X Y he
    have hsub : CFC.sqrt P * (X - Y).val + (X - Y).val * CFC.sqrt P = 0 := by
      simp only [Submodule.coe_sub, Matrix.mul_sub, Matrix.sub_mul]
      calc
        CFC.sqrt P * X.val - CFC.sqrt P * Y.val +
            (X.val * CFC.sqrt P - Y.val * CFC.sqrt P) =
            (CFC.sqrt P * X.val + X.val * CFC.sqrt P) -
              (CFC.sqrt P * Y.val + Y.val * CFC.sqrt P) := by abel
        _ = 0 := sub_eq_zero.mpr he
    exact sub_eq_zero.mp (hz (X - Y) hsub)
  intro X hX
  let C := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ)
    (star hP.isHermitian.eigenvectorUnitary)
  have hd : C (CFC.sqrt P) =
      diagonal (fun i => Real.sqrt (hP.isHermitian.eigenvalues i)) :=
    sqrt_eigenvector_coordinates P hP
  have he := congrArg C hX
  simp only [map_add, map_mul, map_zero, hd] at he
  have hDir := (mem_supportedTangent P X.val).mp X.property
  apply Subtype.ext
  change X.val = 0
  apply C.injective
  rw [map_zero]
  ext i j
  by_cases hi : hP.isHermitian.eigenvalues i = 0
  · exact supported_eigenvector_entry_zero P X.val hP.isHermitian ⟨hDir.2⟩ hDir.1
      i j (Or.inl hi)
  · have hp : 0 < hP.isHermitian.eigenvalues i :=
      lt_of_le_of_ne (hP.eigenvalues_nonneg i) (Ne.symm hi)
    have hden : 0 < Real.sqrt (hP.isHermitian.eigenvalues i) +
        Real.sqrt (hP.isHermitian.eigenvalues j) :=
      add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr hp) (Real.sqrt_nonneg _)
    have hij := congrFun (congrFun he i) j
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.zero_apply] at hij
    have hm : (Real.sqrt (hP.isHermitian.eigenvalues i) +
        Real.sqrt (hP.isHermitian.eigenvalues j)) * C X.val i j = 0 := by
      nlinarith [hij]
    exact (mul_eq_zero.mp hm).resolve_left hden.ne'

/-- If [P is positive semidefinite](hyp:hP), then for any vector x,
[the positive square root of P sends x to zero if and only if P sends x to zero](goal). -/
-- @node: sqrt_mulVec_eq_zero_iff
lemma sqrt_mulVec_eq_zero_iff (P : Matrix ι ι ℝ) (hP : P.PosSemidef) (x : ι → ℝ) :
    CFC.sqrt P *ᵥ x = 0 ↔ P *ᵥ x = 0 := by
  have hs : (CFC.sqrt P).IsHermitian := (CFC.sqrt_nonneg P).posSemidef.isHermitian
  have he := Matrix.conjTranspose_mul_self_mulVec_eq_zero (CFC.sqrt P) x
  simpa only [hs.eq, CFC.sqrt_mul_sqrt_self P hP.nonneg] using he.symm

-- @node: sqrt_mem_supportedTangent
/-- If [P is positive semidefinite](hyp:hP), then [its positive square root
belongs to the fixed-support symmetric space of P](goal). -/
lemma sqrt_mem_supportedTangent (P : Matrix ι ι ℝ) (hP : P.PosSemidef) :
    CFC.sqrt P ∈ supportedTangent P := by
  apply (mem_supportedTangent P _).mpr
  exact ⟨Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg P).posSemidef.isHermitian,
    fun x hx => (sqrt_mulVec_eq_zero_iff P hP x).mpr hx⟩

/-- If [P is positive semidefinite](hyp:hP), then [there is a continuous linear
isomorphism of its fixed-support symmetric space whose action sends X to the sum
of the products of the positive square root of P with X in the two orders](goal). -/
-- @node: sqrt_sylvester_equiv
lemma sqrt_sylvester_equiv (P : Matrix ι ι ℝ) (hP : P.PosSemidef) :
    ∃ e : supportedTangent P ≃L[ℝ] supportedTangent P,
      e.toContinuousLinearMap = supportedJordan P ⟨CFC.sqrt P, sqrt_mem_supportedTangent P hP⟩ := by
  let b : supportedTangent P := ⟨CFC.sqrt P, sqrt_mem_supportedTangent P hP⟩
  let L := supportedJordan P b
  have hi : Function.Injective L := by
    intro X Y he
    apply sqrt_sylvester_supported_injective P hP
    exact congrArg Subtype.val he
  exact ⟨(LinearEquiv.ofInjectiveEndo L.toLinearMap hi).toContinuousLinearEquiv, rfl⟩

/-- If [P is positive semidefinite](hyp:hP), then [there exists a map on its
fixed-support symmetric space that is infinitely differentiable at P, takes P to
its positive square root, and squares to the input throughout some neighborhood
of P](goal). -/
-- @node: exists_smooth_supported_square_inverse
lemma exists_smooth_supported_square_inverse (P : Matrix ι ι ℝ) (hP : P.PosSemidef) :
    let p : supportedTangent P := ⟨P, base_mem_supportedTangent P hP⟩
    let b : supportedTangent P := ⟨CFC.sqrt P, sqrt_mem_supportedTangent P hP⟩
    ∃ g : supportedTangent P → supportedTangent P,
      ContDiffAt ℝ ⊤ g p ∧ g p = b ∧
      ∀ᶠ Q in nhds p, supportedSquare P (g Q) = Q := by
  dsimp only
  let p : supportedTangent P := ⟨P, base_mem_supportedTangent P hP⟩
  let b : supportedTangent P := ⟨CFC.sqrt P, sqrt_mem_supportedTangent P hP⟩
  obtain ⟨e, he⟩ := sqrt_sylvester_equiv P hP
  have hd : HasFDerivAt (supportedSquare P) e.toContinuousLinearMap b := by
    rw [he]
    exact hasFDerivAt_supportedSquare P b
  have hc := (contDiff_supportedSquare P).contDiffAt (x := b)
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hs : supportedSquare P b = p := by
    apply Subtype.ext
    rw [supportedSquare_apply]
    exact CFC.sqrt_mul_sqrt_self P hP.nonneg
  refine ⟨hc.localInverse hd hn, ?_, ?_, ?_⟩
  · simpa only [hs] using hc.to_localInverse hd hn
  · simpa only [hs] using hc.localInverse_apply_image hd hn
  · simpa only [hs, ContDiffAt.localInverse] using
      (hc.hasStrictFDerivAt' hd hn).eventually_right_inverse

/-- For a matrix Q in the fixed-support symmetric space of P and a vector x
orthogonal to the kernel of P, [the vector Qx is also orthogonal to that kernel](goal). -/
-- @node: supportedTangent_maps_support
lemma supportedTangent_maps_support (P : Matrix ι ι ℝ) (Q : supportedTangent P)
    (x : supportSubspace P) : Matrix.toEuclideanLin Q.val x.val ∈ supportSubspace P := by
  intro y hy
  have hQ := (mem_supportedTangent P Q.val).mp Q.property
  have hpy : P *ᵥ WithLp.ofLp y = 0 := by
    simpa only [LinearMap.mem_ker, Matrix.toEuclideanLin_apply, WithLp.toLp_eq_zero] using hy
  have hqy : Matrix.toEuclideanLin Q.val y = 0 := by
    simp only [Matrix.toEuclideanLin_apply, hQ.2 _ hpy, WithLp.toLp_zero]
  rw [← (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (supportedTangent_isHermitian P Q)) y x.val, hqy, inner_zero_left]

/-- For a matrix Q in the fixed-support symmetric space of P, if [Q is strictly
positive on every nonzero vector orthogonal to the kernel of P](hyp:hQ), then
[Q is positive semidefinite on the whole ambient space](goal). -/
-- @node: positiveSupportLocus_posSemidef
lemma positiveSupportLocus_posSemidef (P : Matrix ι ι ℝ) (Q : supportedTangent P)
    (hQ : Q ∈ positiveSupportLocus P) : Q.val.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨supportedTangent_isHermitian P Q, ?_⟩
  intro v
  let x : EuclideanSpace ℝ ι := WithLp.toLp 2 v
  obtain ⟨y, hy, z, hz, hx⟩ :=
    (LinearMap.ker (Matrix.toEuclideanLin P)).exists_add_mem_mem_orthogonal x
  have hpy : P *ᵥ WithLp.ofLp y = 0 := by
    simpa only [LinearMap.mem_ker, Matrix.toEuclideanLin_apply, WithLp.toLp_eq_zero] using hy
  have hqy : Matrix.toEuclideanLin Q.val y = 0 := by
    simp only [Matrix.toEuclideanLin_apply,
      ((mem_supportedTangent P Q.val).mp Q.property).2 _ hpy, WithLp.toLp_zero]
  have hcross : inner ℝ y (Matrix.toEuclideanLin Q.val z) = 0 :=
    supportedTangent_maps_support P Q ⟨z, hz⟩ y hy
  have hn : 0 ≤ inner ℝ z (Matrix.toEuclideanLin Q.val z) := by
    by_cases he : z = 0
    · simp [he]
    · exact (hQ ⟨z, hz⟩ (fun he' => he (congrArg Subtype.val he'))).le
  have hid : star v ⬝ᵥ Q.val *ᵥ v = inner ℝ x (Matrix.toEuclideanLin Q.val x) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
      dotProduct_comm]
  rw [hid, hx, map_add, hqy, zero_add, inner_add_left, hcross, zero_add]
  exact hn

-- @node: sqrt_mem_positiveSupportLocus
/-- If [P is positive semidefinite](hyp:hP), then [its positive square root
belongs to the positive-support locus of P](goal). -/
lemma sqrt_mem_positiveSupportLocus (P : Matrix ι ι ℝ) (hP : P.PosSemidef) :
    (⟨CFC.sqrt P, sqrt_mem_supportedTangent P hP⟩ : supportedTangent P) ∈
      positiveSupportLocus P := by
  intro x hx
  have hInner : inner ℝ x.val (Matrix.toEuclideanLin (CFC.sqrt P) x.val) =
      star (WithLp.ofLp x.val) ⬝ᵥ CFC.sqrt P *ᵥ WithLp.ofLp x.val := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
      dotProduct_comm]
  rw [hInner]
  have hS := (CFC.sqrt_nonneg P).posSemidef
  apply lt_of_le_of_ne (hS.dotProduct_mulVec_nonneg _)
  intro he
  have hs := (hS.dotProduct_mulVec_zero_iff (WithLp.ofLp x.val)).mp he.symm
  have hp := (sqrt_mulVec_eq_zero_iff P hP _).mp hs
  have hker : x.val ∈ LinearMap.ker (Matrix.toEuclideanLin P) := by
    simp only [LinearMap.mem_ker, Matrix.toEuclideanLin_apply, hp, WithLp.toLp_zero]
  have hzero : x.val = 0 := inner_self_eq_zero.mp (x.property x.val hker)
  exact hx (Subtype.ext hzero)

/-- If [P is positive semidefinite](hyp:hP), then [the positive matrix square-root
map, restricted to the fixed-support symmetric space of P, is infinitely
differentiable at P](goal). -/
-- @node: contDiffAt_supported_sqrt
lemma contDiffAt_supported_sqrt (P : Matrix ι ι ℝ) (hP : P.PosSemidef) :
    ContDiffAt ℝ ⊤ (fun Q : supportedTangent P => CFC.sqrt Q.val)
      ⟨P, base_mem_supportedTangent P hP⟩ := by
  let p : supportedTangent P := ⟨P, base_mem_supportedTangent P hP⟩
  let b : supportedTangent P := ⟨CFC.sqrt P, sqrt_mem_supportedTangent P hP⟩
  obtain ⟨g, hc, hg, hi⟩ := exists_smooth_supported_square_inverse P hP
  have hpos : ∀ᶠ Q in nhds p, g Q ∈ positiveSupportLocus P := by
    apply hc.continuousAt.preimage_mem_nhds
    rw [hg]
    exact (isOpen_positiveSupportLocus P).mem_nhds (sqrt_mem_positiveSupportLocus P hP)
  have he : (fun Q : supportedTangent P => CFC.sqrt Q.val) =ᶠ[nhds p]
      (fun Q => (g Q).val) := by
    filter_upwards [hi, hpos] with Q hsq hpos
    have hgpos := positiveSupportLocus_posSemidef P (g Q) hpos
    have hsqval : (g Q).val * (g Q).val = Q.val := by
      simpa only [supportedSquare_apply] using congrArg Subtype.val hsq
    have hQ : Q.val.PosSemidef := hsqval ▸
      hermitian_square_posSemidef (g Q).val hgpos.isHermitian
    exact (CFC.sqrt_eq_iff Q.val (g Q).val hQ.nonneg hgpos.nonneg).mpr
      (by simpa only [sq] using hsqval)
  have hval : ContDiffAt ℝ ⊤ (fun Q => (g Q).val) p := by
    exact (supportedTangent P).subtypeL.contDiff.comp_contDiffAt p hc
  exact hval.congr_of_eventuallyEq he


/-- For a matrix Q in the fixed-support symmetric space of P, if [Q is strictly
positive on every nonzero vector orthogonal to the kernel of P](hyp:hQ), then
[every vector annihilated by Q is also annihilated by P](goal). -/
-- @node: positiveSupportLocus_annihilatesKernel
lemma positiveSupportLocus_annihilatesKernel (P : Matrix ι ι ℝ) (Q : supportedTangent P)
    (hQ : Q ∈ positiveSupportLocus P) : AnnihilatesKernel Q.val P := by
  intro v hv
  let x : EuclideanSpace ℝ ι := WithLp.toLp 2 v
  obtain ⟨y, hy, z, hz, hx⟩ :=
    (LinearMap.ker (Matrix.toEuclideanLin P)).exists_add_mem_mem_orthogonal x
  have hpy : P *ᵥ WithLp.ofLp y = 0 := by
    simpa only [LinearMap.mem_ker, Matrix.toEuclideanLin_apply, WithLp.toLp_eq_zero] using hy
  have hqy : Matrix.toEuclideanLin Q.val y = 0 := by
    simp only [Matrix.toEuclideanLin_apply,
      ((mem_supportedTangent P Q.val).mp Q.property).2 _ hpy, WithLp.toLp_zero]
  have hqx : Matrix.toEuclideanLin Q.val x = 0 := by
    simp only [x, Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, hv, WithLp.toLp_zero]
  have hqz : Matrix.toEuclideanLin Q.val z = 0 := by
    simpa only [hx, map_add, hqy, zero_add] using hqx
  have hzero : z = 0 := by
    by_contra hne
    have hp := hQ ⟨z, hz⟩ (fun he => hne (congrArg Subtype.val he))
    rw [hqz, inner_zero_right] at hp
    exact lt_irrefl _ hp
  have hxker : x ∈ LinearMap.ker (Matrix.toEuclideanLin P) := by
    simpa only [hx, hzero, add_zero] using hy
  simpa only [LinearMap.mem_ker, Matrix.toEuclideanLin_apply, x,
    WithLp.ofLp_toLp, WithLp.toLp_eq_zero] using hxker

-- @node: supportedTangent_le_of_positiveSupportLocus
/-- For a matrix Q in the fixed-support symmetric space of P, if [Q is strictly
positive on every nonzero vector orthogonal to the kernel of P](hyp:hQ), then
[the fixed-support symmetric space of P is contained in that of Q](goal). -/
lemma supportedTangent_le_of_positiveSupportLocus (P : Matrix ι ι ℝ)
    (Q : supportedTangent P) (hQ : Q ∈ positiveSupportLocus P) :
    supportedTangent P ≤ supportedTangent Q.val := by
  intro X hX
  obtain ⟨hs, hk⟩ := (mem_supportedTangent P X).mp hX
  exact (mem_supportedTangent Q.val X).mpr ⟨hs, fun x hx =>
    hk x (positiveSupportLocus_annihilatesKernel P Q hQ x hx)⟩

/-- For any real square matrix P, [the positive matrix square-root map on its
fixed-support symmetric space is infinitely differentiable throughout the
positive-support locus](goal). -/
@[fun_prop]
-- @node: contDiffOn_supported_sqrt
lemma contDiffOn_supported_sqrt (P : Matrix ι ι ℝ) :
    ContDiffOn ℝ ⊤ (fun Q : supportedTangent P => CFC.sqrt Q.val)
      (positiveSupportLocus P) := by
  intro Q hQ
  have hpos := positiveSupportLocus_posSemidef P Q hQ
  have hmem : CFC.sqrt Q.val ∈ supportedTangent P := by
    apply (mem_supportedTangent P _).mpr
    refine ⟨Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg Q.val).posSemidef.isHermitian, ?_⟩
    intro x hx
    exact (sqrt_mulVec_eq_zero_iff Q.val hpos x).mpr
      (((mem_supportedTangent P Q.val).mp Q.property).2 x hx)
  let b : supportedTangent P := ⟨CFC.sqrt Q.val, hmem⟩
  have hb : b ∈ positiveSupportLocus P := by
    intro x hx
    have hInner : inner ℝ x.val (Matrix.toEuclideanLin b.val x.val) =
        star (WithLp.ofLp x.val) ⬝ᵥ b.val *ᵥ WithLp.ofLp x.val := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
        dotProduct_comm]
    rw [hInner]
    have hB := (CFC.sqrt_nonneg Q.val).posSemidef
    apply lt_of_le_of_ne (hB.dotProduct_mulVec_nonneg _)
    intro he
    have hs := (hB.dotProduct_mulVec_zero_iff (WithLp.ofLp x.val)).mp he.symm
    have hq := (sqrt_mulVec_eq_zero_iff Q.val hpos _).mp hs
    have hp := positiveSupportLocus_annihilatesKernel P Q hQ _ hq
    have hk : x.val ∈ LinearMap.ker (Matrix.toEuclideanLin P) := by
      simp only [LinearMap.mem_ker, Matrix.toEuclideanLin_apply, hp, WithLp.toLp_zero]
    exact hx (Subtype.ext (inner_self_eq_zero.mp (x.property x.val hk)))
  have hle := supportedTangent_le_of_positiveSupportLocus P Q hQ
  let L := supportedJordan P b
  have hinj : Function.Injective L := by
    intro X Y he
    have hXY : (⟨X.val, hle X.property⟩ : supportedTangent Q.val) =
        ⟨Y.val, hle Y.property⟩ :=
      sqrt_sylvester_supported_injective Q.val hpos (congrArg Subtype.val he)
    apply Subtype.ext
    exact congrArg (fun Z : supportedTangent Q.val => Z.val) hXY
  let e := (LinearEquiv.ofInjectiveEndo L.toLinearMap hinj).toContinuousLinearEquiv
  have hd : HasFDerivAt (supportedSquare P) e.toContinuousLinearMap b :=
    hasFDerivAt_supportedSquare P b
  have hc := (contDiff_supportedSquare P).contDiffAt (x := b)
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hs : supportedSquare P b = Q := by
    apply Subtype.ext
    rw [supportedSquare_apply]
    exact CFC.sqrt_mul_sqrt_self Q.val hpos.nonneg
  let g := hc.localInverse hd hn
  have hgc : ContDiffAt ℝ ⊤ g Q := by simpa only [hs] using hc.to_localInverse hd hn
  have hg : g Q = b := by simpa only [hs] using hc.localInverse_apply_image hd hn
  have hi : ∀ᶠ R in nhds Q, supportedSquare P (g R) = R := by
    simpa only [hs, g, ContDiffAt.localInverse] using
      (hc.hasStrictFDerivAt' hd hn).eventually_right_inverse
  have hgp : ∀ᶠ R in nhds Q, g R ∈ positiveSupportLocus P := by
    apply hgc.continuousAt.preimage_mem_nhds
    rw [hg]
    exact (isOpen_positiveSupportLocus P).mem_nhds hb
  have he : (fun R : supportedTangent P => CFC.sqrt R.val) =ᶠ[nhds Q]
      (fun R => (g R).val) := by
    filter_upwards [hi, hgp] with R hsq hr
    have hgpos := positiveSupportLocus_posSemidef P (g R) hr
    have hsqval : (g R).val * (g R).val = R.val := by
      simpa only [supportedSquare_apply] using congrArg Subtype.val hsq
    have hR : R.val.PosSemidef := hsqval ▸
      hermitian_square_posSemidef (g R).val hgpos.isHermitian
    exact (CFC.sqrt_eq_iff R.val (g R).val hR.nonneg hgpos.nonneg).mpr
      (by simpa only [sq] using hsqval)
  have hval : ContDiffAt ℝ ⊤ (fun R => (g R).val) Q :=
    (supportedTangent P).subtypeL.contDiff.comp_contDiffAt Q hgc
  exact (hval.congr_of_eventuallyEq he).contDiffWithinAt

/-- If [P is positive semidefinite](hyp:hP), then [its matrix energy equals the
trace of the product of P with its positive square root](goal). -/
-- @node: matrixEnergy_eq_trace_mul_sqrt
lemma matrixEnergy_eq_trace_mul_sqrt (P : Matrix ι ι ℝ) (hP : P.PosSemidef) :
    matrixEnergy P = (P * CFC.sqrt P).trace := by
  have hs : CFC.sqrt P = cfc Real.sqrt P := by
    rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ P]
    unfold Real.sqrt
    rfl
  unfold matrixEnergy
  congr 1
  calc
    cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) P = cfc (fun x : ℝ => x * Real.sqrt x) P := by
      apply cfc_congr
      intro x hx
      have hn : 0 ≤ x := spectrum_nonneg_of_nonneg hP.nonneg hx
      dsimp only
      rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add' hn (by norm_num), Real.rpow_one]
    _ = P * CFC.sqrt P := by
      rw [cfc_mul (fun x : ℝ => x) Real.sqrt P, cfc_id' (R := ℝ) P, ← hs]

/-- For any real square matrix P, [matrix energy, restricted to its fixed-support
symmetric space, is infinitely differentiable throughout the positive-support
locus](goal). -/
-- @node: contDiffOn_supported_matrixEnergy
lemma contDiffOn_supported_matrixEnergy (P : Matrix ι ι ℝ) :
    ContDiffOn ℝ ⊤ (fun Q : supportedTangent P => matrixEnergy Q.val)
      (positiveSupportLocus P) := by
  let tr : Matrix ι ι ℝ →L[ℝ] ℝ := (Matrix.traceLinearMap ι ℝ ℝ).toContinuousLinearMap
  have hc : ContDiffOn ℝ ⊤ (fun Q : supportedTangent P =>
      tr (Q.val * CFC.sqrt Q.val)) (positiveSupportLocus P) := by
    apply tr.contDiff.comp_contDiffOn
    exact (supportedTangent P).subtypeL.contDiff.contDiffOn.mul
      (contDiffOn_supported_sqrt P)
  apply hc.congr
  intro Q hQ
  exact matrixEnergy_eq_trace_mul_sqrt Q.val (positiveSupportLocus_posSemidef P Q hQ)

end Papers.OaiBoundDyadicTriangular
