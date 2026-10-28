module

public import Papers.OaiBoundDyadicTriangular.Helpers.SupportedCalculus
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-! # Derivatives of the supported square root and trace energy -/

@[expose] public section

open Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace MatrixOrder Topology

namespace Papers.OaiBoundDyadicTriangular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @node: differentiableAt_supported_sqrt
/-- If [Q is strictly positive on the support of P](hyp:hQ), [the matrix square-root
map, restricted to symmetric matrices annihilating the kernel of P, is differentiable
at Q](goal). -/
lemma differentiableAt_supported_sqrt (P : Matrix ι ι ℝ) (Q : supportedTangent P)
    (hQ : Q ∈ positiveSupportLocus P) :
    DifferentiableAt ℝ (fun R : supportedTangent P => CFC.sqrt R.val) Q := by
  exact ((contDiffOn_supported_sqrt P Q hQ).contDiffAt
    ((isOpen_positiveSupportLocus P).mem_nhds hQ)).differentiableAt (by simp)

-- @node: fderiv_supported_sqrt_sylvester
/-- If [Q is strictly positive on the support of P](hyp:hQ), [the derivative X of
the supported square-root map at Q in direction L satisfies the Sylvester equation:
the square root of Q times X plus X times the square root of Q equals L](goal). -/
lemma fderiv_supported_sqrt_sylvester (P : Matrix ι ι ℝ) (Q L : supportedTangent P)
    (hQ : Q ∈ positiveSupportLocus P) :
    let X := fderiv ℝ (fun R : supportedTangent P => CFC.sqrt R.val) Q L
    CFC.sqrt Q.val * X + X * CFC.sqrt Q.val = L.val := by
  dsimp only
  have hd := (differentiableAt_supported_sqrt P Q hQ).hasFDerivAt
  have he : (fun R : supportedTangent P => CFC.sqrt R.val * CFC.sqrt R.val)
      =ᶠ[nhds Q] (fun R => R.val) := by
    filter_upwards [(isOpen_positiveSupportLocus P).mem_nhds hQ] with R hR
    exact CFC.sqrt_mul_sqrt_self R.val (positiveSupportLocus_posSemidef P R hR).nonneg
  have hh := (hd.mul' hd).congr_of_eventuallyEq he.symm
  have hh' := hh.unique ((supportedTangent P).subtypeL.hasFDerivAt (x := Q))
  have hv := congrArg (fun A => A L) hh'
  simpa using hv

-- @node: trace_energy_derivative_of_sylvester
/-- If [B squared equals Q](hyp:hsq) and [B times X plus X times B equals K](hyp:hX),
[the trace of K times B plus Q times X equals three halves of the trace of B times
K](goal). -/
lemma trace_energy_derivative_of_sylvester (B Q K X : Matrix ι ι ℝ)
    (hsq : B * B = Q) (hX : B * X + X * B = K) :
    (K * B + Q * X).trace = (3 / 2 : ℝ) * (B * K).trace := by
  have ht : (B * K).trace = 2 * (Q * X).trace := by
    rw [← hX, Matrix.mul_add, Matrix.trace_add, ← Matrix.mul_assoc, hsq,
      ← Matrix.mul_assoc, Matrix.trace_mul_cycle B X B, hsq]
    ring
  rw [Matrix.trace_add, Matrix.trace_mul_comm K B]
  linarith

-- @node: fderiv_supported_matrixEnergy
/-- If [Q is strictly positive on the support of P](hyp:hQ), [the derivative of
the supported trace energy at Q in direction L equals three halves of the trace
of the square root of Q times L](goal). -/
lemma fderiv_supported_matrixEnergy (P : Matrix ι ι ℝ) (Q L : supportedTangent P)
    (hQ : Q ∈ positiveSupportLocus P) :
    fderiv ℝ (fun R : supportedTangent P => matrixEnergy R.val) Q L =
      (3 / 2 : ℝ) * (CFC.sqrt Q.val * L.val).trace := by
  let tr : Matrix ι ι ℝ →L[ℝ] ℝ := (Matrix.traceLinearMap ι ℝ ℝ).toContinuousLinearMap
  have hd := (differentiableAt_supported_sqrt P Q hQ).hasFDerivAt
  have hm := (supportedTangent P).subtypeL.hasFDerivAt (x := Q)
  have hp := tr.hasFDerivAt.comp Q (hm.mul' hd)
  have he : (fun R : supportedTangent P => matrixEnergy R.val) =ᶠ[nhds Q]
      (fun R => tr (R.val * CFC.sqrt R.val)) := by
    filter_upwards [(isOpen_positiveSupportLocus P).mem_nhds hQ] with R hR
    exact matrixEnergy_eq_trace_mul_sqrt R.val (positiveSupportLocus_posSemidef P R hR)
  have hh := (hp.congr_of_eventuallyEq he).fderiv
  rw [hh]
  change (Q.val * (fderiv ℝ (fun R : supportedTangent P => CFC.sqrt R.val) Q L) +
    L.val * CFC.sqrt Q.val).trace = _
  rw [add_comm]
  exact trace_energy_derivative_of_sylvester _ _ _ _
    (CFC.sqrt_mul_sqrt_self Q.val (positiveSupportLocus_posSemidef P Q hQ).nonneg)
    (fderiv_supported_sqrt_sylvester P Q L hQ)

-- @node: supportedEnergyGradient
/-- For [a real square matrix P fixing the support](hyp:P), [the supported energy
gradient map](goal) is built from [the bilinear pairing that sends matrices B and
symmetric directions L annihilating the kernel of P to three halves of the trace
of B times L](step:1), [viewed as a continuous linear map from B to continuous
linear functionals of L](step:2). -/
noncomputable def supportedEnergyGradient (P : Matrix ι ι ℝ) :
    Matrix ι ι ℝ →L[ℝ] (supportedTangent P →L[ℝ] ℝ) :=
  let A : Matrix ι ι ℝ →ₗ[ℝ] (supportedTangent P →ₗ[ℝ] ℝ) :=
    LinearMap.mk₂ ℝ (fun B L => (3 / 2 : ℝ) * (B * L.val).trace)
      (by intros; simp [Matrix.add_mul, Matrix.trace_add, mul_add])
      (by intros; simp [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]; ring)
      (by intros; simp [Matrix.mul_add, Matrix.trace_add, mul_add])
      (by intros; simp [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]; ring)
  (LinearMap.toContinuousLinearMap.toLinearMap.comp A).toContinuousLinearMap

-- @node: supportedEnergyGradient_apply
/-- [Evaluating the supported energy gradient map at a matrix B and a supported
direction L gives three halves of the trace of B times L](goal). -/
lemma supportedEnergyGradient_apply (P B : Matrix ι ι ℝ) (L : supportedTangent P) :
    supportedEnergyGradient P B L = (3 / 2 : ℝ) * (B * L.val).trace := rfl

-- @node: fderiv_two_supported_matrixEnergy
/-- If [Q is strictly positive on the support of P](hyp:hQ), [the second derivative
of the supported trace energy at Q, evaluated twice in direction L, equals the
supported spectral Hessian form at Q in direction L](goal). -/
lemma fderiv_two_supported_matrixEnergy (P : Matrix ι ι ℝ) (Q L : supportedTangent P)
    (hQ : Q ∈ positiveSupportLocus P) :
    fderiv ℝ (fderiv ℝ (fun R : supportedTangent P => matrixEnergy R.val)) Q L L =
      hessForm Q.val (supportedTangent_isHermitian P Q) L.val := by
  have hd := (differentiableAt_supported_sqrt P Q hQ).hasFDerivAt
  have hp := (supportedEnergyGradient P).hasFDerivAt.comp Q hd
  have he : fderiv ℝ (fun R : supportedTangent P => matrixEnergy R.val) =ᶠ[nhds Q]
      (fun R : supportedTangent P => supportedEnergyGradient P (CFC.sqrt R.val)) := by
    filter_upwards [(isOpen_positiveSupportLocus P).mem_nhds hQ] with R hR
    ext M
    exact fderiv_supported_matrixEnergy P R M hR
  rw [(hp.congr_of_eventuallyEq he).fderiv]
  change (3 / 2 : ℝ) *
    ((fderiv ℝ (fun R : supportedTangent P => CFC.sqrt R.val) Q L) * L.val).trace = _
  have hpos := positiveSupportLocus_posSemidef P Q hQ
  have hL := (mem_supportedTangent Q.val L.val).mp
    (supportedTangent_le_of_positiveSupportLocus P Q hQ L.property)
  rw [hessForm_eq_trace_of_sylvester Q.val L.val _ hpos hL.1 ⟨hL.2⟩
    (fderiv_supported_sqrt_sylvester P Q L hQ), hL.1.eq, Matrix.trace_mul_comm]

-- @node: hessForm_nonneg
/-- If [P is symmetric](hyp:hP), [its supported spectral Hessian form is
nonnegative in every real matrix direction K](goal). -/
lemma hessForm_nonneg (P K : Matrix ι ι ℝ) (hP : P.IsHermitian) :
    0 ≤ hessForm P hP K := by
  unfold hessForm
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact div_nonneg (sq_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · exact le_rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- @node: supported_line_hasDerivAt
/-- If [s is open](hyp:hs), [the real-valued function Φ is infinitely differentiable
on s](hyp:hΦ), and [the point p plus t times d lies in s](hyp:ht), [the restriction
of Φ to the line through p in direction d has derivative equal to the first
derivative of Φ applied to d at that point, and this first line derivative has
derivative equal to the second derivative of Φ applied twice to d](goal). -/
lemma supported_line_hasDerivAt (Φ : E → ℝ) (p d : E) (s : Set E)
    (hs : IsOpen s) (hΦ : ContDiffOn ℝ ⊤ Φ s) (t : ℝ) (ht : p + t • d ∈ s) :
    HasDerivAt (fun r : ℝ => Φ (p + r • d)) (fderiv ℝ Φ (p + t • d) d) t ∧
    HasDerivAt (fun r : ℝ => fderiv ℝ Φ (p + r • d) d)
      (fderiv ℝ (fderiv ℝ Φ) (p + t • d) d d) t := by
  have hpath : HasDerivAt (fun r : ℝ => p + r • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add p
  have hc := hΦ.contDiffAt (hs.mem_nhds ht)
  constructor
  · exact (hc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hpath
  · have hfd := (hΦ.fderiv_of_isOpen hs (m := 1) (by simp)).contDiffAt (hs.mem_nhds ht)
    have hh := hfd.differentiableAt (by norm_num)
    have h := (hh.hasFDerivAt.comp_hasDerivAt t hpath).clm_apply (hasDerivAt_const t d)
    simpa using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @node: matrixEnergy_line_continuous
/-- If [T is symmetric](hyp:hT) and [U is symmetric](hyp:hU), [the trace energy
of T plus t times U is a continuous function of the real scalar t](goal). -/
@[fun_prop] lemma matrixEnergy_line_continuous (T U : Matrix ι ι ℝ)
    (hT : T.IsHermitian) (hU : U.IsHermitian) :
    Continuous (fun t : ℝ => matrixEnergy (T + t • U)) := by
  unfold matrixEnergy
  have ha : Continuous (fun t : ℝ => T + t • U) := by fun_prop
  have hc : Continuous (fun t : ℝ => cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) (T + t • U)) := by
    refine Continuous.cfc_of_mem_nhdsSet (s := Set.univ) _ (by simp) ha ?_ ?_
    · intro t
      exact hT.add (hU.smul (by rfl))
    · exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).continuousOn
  exact (Matrix.traceLinearMap ι ℝ ℝ).continuous_of_finiteDimensional.comp hc


-- @node: convex_positiveSupportLocus
/-- [The symmetric matrices annihilating the kernel of P and strictly positive
on its support form a convex set](goal). -/
lemma convex_positiveSupportLocus (P : Matrix ι ι ℝ) :
    Convex ℝ (positiveSupportLocus P) := by
  apply convex_iff_forall_pos.mpr
  intro A hA B hB a b ha hb hab
  intro x hx
  change 0 < inner ℝ x.val (Matrix.toEuclideanLin (a • A.val + b • B.val) x.val)
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    inner_add_right, real_inner_smul_right]
  exact add_pos (mul_pos ha (hA x hx)) (mul_pos hb (hB x hx))

-- @node: convexOn_supported_matrixEnergy
/-- [The trace energy is convex on the set of symmetric matrices annihilating
the kernel of P and strictly positive on its support](goal). -/
lemma convexOn_supported_matrixEnergy (P : Matrix ι ι ℝ) :
    ConvexOn ℝ (positiveSupportLocus P)
      (fun Q : supportedTangent P => matrixEnergy Q.val) := by
  refine ⟨convex_positiveSupportLocus P, ?_⟩
  intro A hA B hB a b ha hb hab
  let Φ := fun Q : supportedTangent P => matrixEnergy Q.val
  let D := B - A
  let f := fun t : ℝ => Φ (A + t • D)
  let f' := fun t : ℝ => fderiv ℝ Φ (A + t • D) D
  let f'' := fun t : ℝ => fderiv ℝ (fderiv ℝ Φ) (A + t • D) D D
  have hm (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      A + t • D ∈ positiveSupportLocus P := by
    have he : A + t • D = (1 - t) • A + t • B := by dsimp [D]; module
    rw [he]
    exact convex_positiveSupportLocus P hA hB (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt f (f' t) t ∧ HasDerivAt f' (f'' t) t :=
    supported_line_hasDerivAt Φ A D _ (isOpen_positiveSupportLocus P)
      (contDiffOn_supported_matrixEnergy P) t (hm t ht)
  have hc : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hd t ht).1.continuousAt.continuousWithinAt
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) hc
    · intro t ht
      exact (hd t (interior_subset ht)).1.hasDerivWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).2.hasDerivWithinAt
    · intro t ht
      dsimp only [f'']
      rw [fderiv_two_supported_matrixEnergy P _ D (hm t (interior_subset ht))]
      exact hessForm_nonneg _ _ _
  have hh := hconv.2 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num) ha hb hab
  have he : A + b • D = a • A + b • B := by
    have ha' : a = 1 - b := by linarith
    dsimp [D]
    rw [ha']
    module
  simpa only [f, Φ, smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero,
    one_smul, D, add_sub_cancel, he] using hh

-- @node: isHermitian_mem_supportedTangent_one
/-- If [A is symmetric](hyp:hA), [A belongs to the supported tangent space of
the identity matrix](goal). -/
lemma isHermitian_mem_supportedTangent_one (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    A ∈ supportedTangent (1 : Matrix ι ι ℝ) := by
  apply (mem_supportedTangent _ _).mpr
  refine ⟨Matrix.isHermitian_iff_isSymm.mp hA, ?_⟩
  intro x hx
  simp only [Matrix.one_mulVec] at hx
  simp [hx]

-- @node: posDef_mem_positiveSupportLocus_one
/-- If [Q is positive definite](hyp:hQ), [it belongs to the positive support
locus of the identity matrix](goal). -/
lemma posDef_mem_positiveSupportLocus_one (Q : supportedTangent (1 : Matrix ι ι ℝ))
    (hQ : Q.val.PosDef) : Q ∈ positiveSupportLocus (1 : Matrix ι ι ℝ) := by
  intro x hx
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
    dotProduct_comm]
  apply hQ.dotProduct_mulVec_pos
  intro hz
  exact hx (Subtype.ext (by simpa using hz))

-- @node: matrixEnergy_convex_combination_posDef
/-- If [A is positive definite](hyp:hA), [B is positive definite](hyp:hB),
[a is nonnegative](hyp:ha), [b is nonnegative](hyp:hb), and [a and b sum to
one](hyp:hab), [the trace energy of a times A plus b times B is at most a times
the energy of A plus b times the energy of B](goal). -/
lemma matrixEnergy_convex_combination_posDef (A B : Matrix ι ι ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    matrixEnergy (a • A + b • B) ≤ a * matrixEnergy A + b * matrixEnergy B := by
  let A' : supportedTangent (1 : Matrix ι ι ℝ) :=
    ⟨A, isHermitian_mem_supportedTangent_one A hA.isHermitian⟩
  let B' : supportedTangent (1 : Matrix ι ι ℝ) :=
    ⟨B, isHermitian_mem_supportedTangent_one B hB.isHermitian⟩
  exact (convexOn_supported_matrixEnergy (1 : Matrix ι ι ℝ)).2
    (posDef_mem_positiveSupportLocus_one A' hA)
    (posDef_mem_positiveSupportLocus_one B' hB) ha hb hab

-- @node: convexOn_matrixEnergy
/-- [The trace energy is convex on the cone of positive semidefinite real
matrices](goal). -/
lemma convexOn_matrixEnergy :
    ConvexOn ℝ {A : Matrix ι ι ℝ | A.PosSemidef} matrixEnergy := by
  have hcone : Convex ℝ {A : Matrix ι ι ℝ | A.PosSemidef} := by
    intro A hA B hB a b ha hb hab
    exact (hA.smul ha).add (hB.smul hb)
  refine ⟨hcone, ?_⟩
  intro A hA B hB a b ha hb hab
  let C := a • A + b • B
  have hC : C.PosSemidef := hcone hA hB ha hb hab
  have hlim (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
      Tendsto (fun η : ℝ => matrixEnergy (M + η • 1)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (matrixEnergy M)) := by
    simpa only [zero_smul, add_zero] using
      ((matrixEnergy_line_continuous M 1 hM Matrix.isHermitian_one).continuousAt (x := 0)).tendsto.mono_left
        nhdsWithin_le_nhds
  have hineq : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioi 0),
      matrixEnergy (C + η • 1) ≤
        a * matrixEnergy (A + η • 1) + b * matrixEnergy (B + η • 1) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hηpos : (η • (1 : Matrix ι ι ℝ)).PosDef := Matrix.PosDef.one.smul hη
    have h := matrixEnergy_convex_combination_posDef (A + η • 1) (B + η • 1)
      (Matrix.PosDef.posSemidef_add hA hηpos) (Matrix.PosDef.posSemidef_add hB hηpos)
      a b ha hb hab
    have he : a • (A + η • 1) + b • (B + η • 1) = C + η • 1 := by
      dsimp [C]
      rw [smul_add, smul_add, smul_smul, smul_smul]
      have hcoeff : a * η + b * η = η := by rw [← add_mul, hab, one_mul]
      calc
        a • A + (a * η) • 1 + (b • B + (b * η) • 1) =
            a • A + b • B + (a * η + b * η) • 1 := by rw [add_smul]; abel
        _ = _ := by rw [hcoeff]
    rwa [he] at h
  exact le_of_tendsto_of_tendsto (hlim C hC.isHermitian)
    (((hlim A hA.isHermitian).const_mul a).add ((hlim B hB.isHermitian).const_mul b)) hineq

end Papers.OaiBoundDyadicTriangular
