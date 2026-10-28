module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.ReductionHessian
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # The determinant calculation in the adapted basis -/

@[expose] public section

noncomputable section

open Set Matrix Filter
open scoped Topology
open scoped ContDiff BigOperators

namespace OaiSmoothNonquadraticAffine

-- @node: spatialTimeBlock
/-- For [a spatial matrix A](hyp:A) and [a real time entry d](hyp:d), the
[spatial-time block matrix](goal) has A as its spatial block, d as its last
diagonal entry, and zeros in the mixed spatial-time entries. -/
def spatialTimeBlock {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (d : ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => Fin.lastCases (Fin.lastCases d (fun _ => 0) j)
    (fun a => Fin.lastCases 0 (fun b => A a b) j) i

-- @node: spatialTimeBlock_det
/-- [The determinant of the matrix with spatial block A, last diagonal entry d,
and zero mixed entries equals the determinant of A multiplied by d](goal). -/
lemma spatialTimeBlock_det {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (d : ℝ) :
    (spatialTimeBlock A d).det = A.det * d := by
  have hminor : (spatialTimeBlock A d).submatrix Fin.castSucc Fin.castSucc = A := by
    ext i j
    simp [spatialTimeBlock]
  rw [Matrix.det_succ_column _ (Fin.last m), Fin.sum_univ_castSucc]
  simp [spatialTimeBlock, Fin.succAbove_last, hminor, mul_comm]

-- @node: adaptedFrame
/-- For [a spatial function F](hyp:F), [a point z with spatial coordinates x and
time coordinate t](hyp:z), [positivity of F at x](hyp:hF), and [a coordinate
index i](hyp:i), the [i-th adapted frame vector](goal) is the time unit vector
when i is the last index; otherwise it is the i-th spatial unit vector plus
(t/F(x)) times the i-th partial derivative of F at x times the time unit vector. -/
def adaptedFrame {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (z : EuclideanSpace ℝ (Fin (m + 1))) (hF : 0 < F (xPart z))
    (i : Fin (m + 1)) : EuclideanSpace ℝ (Fin (m + 1)) :=
  Fin.lastCases (timeBasis m) (adaptedSpatialBasis F z hF) i

-- @node: adaptedFrameMatrix
/-- For [a spatial function F](hyp:F), [a space-time point z](hyp:z), and
[positivity of F at the spatial coordinates of z](hyp:hF), the
[adapted frame matrix](goal) has the adapted frame vectors as its columns. -/
def adaptedFrameMatrix {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (z : EuclideanSpace ℝ (Fin (m + 1))) (hF : 0 < F (xPart z)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => adaptedFrame F z hF j i

-- @node: adaptedFrameMatrix_det
/-- If [F is positive at the spatial coordinates of z](hyp:hF), then
[the adapted frame matrix at z has determinant one](goal). -/
lemma adaptedFrameMatrix_det {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (z : EuclideanSpace ℝ (Fin (m + 1))) (hF : 0 < F (xPart z)) :
    (adaptedFrameMatrix F z hF).det = 1 := by
  let c : Fin (m + 1) → ℝ := Fin.lastCases 0
    (fun i => reductionZeta F z hF * fderiv ℝ F (xPart z) (EuclideanSpace.single i 1))
  have heq := Matrix.det_eq_of_forall_row_eq_smul_add_const
    (A := (adaptedFrameMatrix F z hF)ᵀ) (B := 1) c (Fin.last m) (by simp [c])
  rw [Matrix.det_transpose, Matrix.det_one] at heq
  apply heq
  intro i j
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp [adaptedFrameMatrix, adaptedFrame, timeBasis, c, Matrix.one_apply, eq_comm]
  · simp [adaptedFrameMatrix, adaptedFrame, adaptedSpatialBasis, spatialBasis, timeBasis,
      c, Matrix.one_apply, eq_comm]

-- @node: hessian_congruence_entry
/-- If [f is twice continuously differentiable at z](hyp:hf), then
[the entry in row i and column j of the transpose of M times the Hessian of f
times M equals the second differential of f at z applied to columns i and j
of M](goal). -/
lemma hessian_congruence_entry {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {z : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ 2 f z) (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Mᵀ * hessianMatrix f z * M) i j =
      secondDifferential f z (WithLp.toLp 2 (fun a => M a i))
        (WithLp.toLp 2 (fun a => M a j)) := by
  rw [secondDifferential_eq_dotProduct hf]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

-- @node: reductionGraph_hessian_congruence
/-- Suppose [Ω is open and F and P are smooth and positive on Ω](hyp:hFP),
[the spatial coordinates x of z lie in Ω](hyp:hz), and [F(x) is positive](hyp:hF).
[In the adapted frame, the Hessian of the reduction graph u has spatial block
(F(x)/u(z)) times the Hessian of F at x, time entry F(x)²/u(z)³, and zero
mixed spatial-time entries](goal). -/
lemma reductionGraph_hessian_congruence {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) (hF : 0 < F (xPart z)) :
    (adaptedFrameMatrix F z hF)ᵀ * hessianMatrix (reductionGraph F) z *
      adaptedFrameMatrix F z hF =
    spatialTimeBlock ((F (xPart z) / reductionGraph F z) • hessianMatrix F (xPart z))
      (F (xPart z) ^ 2 / reductionGraph F z ^ 3) := by
  have hu : ContDiffAt ℝ 2 (reductionGraph F) z :=
    (reductionGraph_contDiffAt hFP hz).of_le (by decide)
  ext i j
  rw [hessian_congruence_entry hu]
  change secondDifferential (reductionGraph F) z (adaptedFrame F z hF i)
    (adaptedFrame F z hF j) = _
  refine Fin.lastCases ?_ (fun a => ?_) i <;>
    refine Fin.lastCases ?_ (fun b => ?_) j
  · simpa [adaptedFrame, spatialTimeBlock] using reductionGraph_time_time hFP hz
  · simp only [adaptedFrame, spatialTimeBlock, Fin.lastCases_last, Fin.lastCases_castSucc]
    rw [show secondDifferential (reductionGraph F) z (timeBasis m)
      (adaptedSpatialBasis F z hF b) = secondDifferential (reductionGraph F) z
        (adaptedSpatialBasis F z hF b) (timeBasis m) from
          hu.isSymmSndFDerivAt (by norm_num) _ _]
    exact reductionGraph_adapted_mixed hFP hz hF b
  · simpa [adaptedFrame, spatialTimeBlock] using reductionGraph_adapted_mixed hFP hz hF a
  · simpa [adaptedFrame, spatialTimeBlock] using reductionGraph_adapted_spatial hFP hz hF a b

-- @node: reductionGraph_det
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP) and
[the spatial coordinates x of z lie in Ω](hyp:hz), then [the Hessian determinant
of the reduction graph u at z equals F(x) to the power m + 2 times u(z) to the
power −(m + 3) times the Hessian determinant of F at x](goal). -/
lemma reductionGraph_det {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) :
    (hessianMatrix (reductionGraph F) z).det =
      F (xPart z) ^ (m + 2) * (reductionGraph F z) ^ (-((m : ℝ) + 3)) *
        (hessianMatrix F (xPart z)).det := by
  have hF := (hFP.2.2.2 _ hz).1
  have hu : 0 < reductionGraph F z := by
    unfold reductionGraph
    positivity
  have hd := congrArg Matrix.det (reductionGraph_hessian_congruence hFP hz hF)
  simp only [Matrix.det_mul, Matrix.det_transpose, adaptedFrameMatrix_det, one_mul, mul_one,
    spatialTimeBlock_det, Matrix.det_smul, Fintype.card_fin] at hd
  rw [hd]
  rw [Real.rpow_neg hu.le, show (m : ℝ) + 3 = ((m + 3 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast]
  rw [div_pow, pow_add, pow_add]
  field_simp

-- @node: reduction_affineWeight_eq
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP),
[F and P satisfy the reduced system on Ω](hyp:hSystem), and [the spatial
coordinates x of z lie in Ω](hyp:hz), then [the affine weight of the reduction
graph at z equals P(x) times the scalar reduction factor evaluated at t/F(x),
where t is the time coordinate of z](goal). -/
lemma reduction_affineWeight_eq {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) (hSystem : ReducedSystem m Ω F P)
    {z : EuclideanSpace ℝ (Fin (m + 1))} (hz : xPart z ∈ Ω) :
    affineWeight (m + 1) (reductionGraph F) z =
      P (xPart z) * reductionH m (tPart z / F (xPart z)) :=
  reduction_weight_from_det hFP hSystem z hz (reductionGraph_det hFP hz)

-- @node: secondDifferential_congr
/-- If [f and g agree on a neighborhood of z](hyp:heq), then [their second
differentials at z agree on any pair of directions v and w](goal). -/
lemma secondDifferential_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {z : E} (heq : f =ᶠ[𝓝 z] g) (v w : E) :
    secondDifferential f z v w = secondDifferential g z v w := by
  exact congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L v w)
    (heq.fderiv (𝕜 := ℝ)).fderiv_eq

-- @node: secondDifferential_scalar_comp
/-- If [q is twice continuously differentiable at z](hyp:hq) and [the scalar
function h is twice continuously differentiable everywhere](hyp:hh), then
[the second differential of h composed with q at z in directions v and w
equals h′(q(z)) times the second differential of q in those directions plus
h″(q(z)) times the product of the directional derivatives of q along v and w](goal). -/
lemma secondDifferential_scalar_comp {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {q : E → ℝ} {h : ℝ → ℝ} {z : E}
    (hq : ContDiffAt ℝ 2 q z) (hh : ContDiff ℝ 2 h) (v w : E) :
    secondDifferential (fun y => h (q y)) z v w =
      deriv h (q z) * secondDifferential q z v w +
        deriv (deriv h) (q z) * fderiv ℝ q z v * fderiv ℝ q z w := by
  have heq : (fun y => fderiv ℝ (fun a => h (q a)) y w) =ᶠ[𝓝 z]
      (fun y => deriv h (q y) * fderiv ℝ q y w) := by
    filter_upwards [hq.eventually (by norm_num)] with y hy
    have hd := (hh.differentiable (by norm_num) (q y)).hasDerivAt.comp_hasFDerivAt y
      (hy.differentiableAt (by norm_num)).hasFDerivAt
    rw [show fderiv ℝ (fun a => h (q a)) y = _ from hd.fderiv]
    rfl
  have hdh : DifferentiableAt ℝ (fun y => deriv h (q y)) z :=
    (hh.differentiable_deriv_two (q z)).comp z (hq.differentiableAt (by norm_num))
  have hdq := (hq.fderiv_right (by norm_num)).differentiableAt_one.clm_apply
    (differentiableAt_const w)
  have hc : ContDiffAt ℝ 2 (fun y => h (q y)) z := hh.contDiffAt.comp z hq
  rw [secondDifferential_eq hc, heq.fderiv_eq,
    fderiv_fun_mul hdh hdq]
  have hd := (hh.differentiable_deriv_two (q z)).hasDerivAt.comp_hasFDerivAt z
    (hq.differentiableAt (by norm_num)).hasFDerivAt
  rw [show fderiv ℝ (fun y => deriv h (q y)) z = _ from hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    ← secondDifferential_eq hq]
  ring

-- @node: normalizedTime
/-- For [a spatial function F](hyp:F) and [a point z with spatial coordinates x
and time coordinate t](hyp:z), the [normalized time](goal) is t divided by F(x). -/
def normalizedTime {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (z : EuclideanSpace ℝ (Fin (m + 1))) : ℝ := tPart z / F (xPart z)

-- @node: normalizedTime_contDiffAt
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP) and
[the spatial coordinates of z lie in Ω](hyp:hz), then [normalized time is
infinitely differentiable at z](goal). -/
@[fun_prop] lemma normalizedTime_contDiffAt {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) : ContDiffAt ℝ ∞ (normalizedTime F) z := by
  have hf := hFP.2.1.contDiffAt (hFP.1.mem_nhds hz)
  have hF := (hFP.2.2.2 _ hz).1.ne'
  unfold normalizedTime
  fun_prop

-- @node: normalizedTime_fderiv
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP) and
[the spatial coordinates x of z lie in Ω](hyp:hz), then [the derivative of
normalized time at z along v equals the time component of v minus normalized
time at z times the derivative of F at x along the spatial component of v,
all divided by F(x)](goal). -/
lemma normalizedTime_fderiv {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) (v : EuclideanSpace ℝ (Fin (m + 1))) :
    fderiv ℝ (normalizedTime F) z v =
      (tPart v - normalizedTime F z * fderiv ℝ F (xPart z) (xPart v)) / F (xPart z) := by
  have hf := (hFP.2.1.contDiffAt (hFP.1.mem_nhds hz)).differentiableAt (by decide)
  have hF := (hFP.2.2.2 _ hz).1.ne'
  let L := xProjection m
  let T := EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)
  have hd := T.hasFDerivAt.mul
    ((hasDerivAt_inv hF).comp_hasFDerivAt z (hf.hasFDerivAt.comp z L.hasFDerivAt))
  have hn : normalizedTime F = T * ((fun s : ℝ => s⁻¹) ∘ F ∘ xPart) := by
    funext y
    exact div_eq_mul_inv _ _
  rw [hn, hd.fderiv]
  simp only [_root_.smul_apply, _root_.add_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  change tPart z * (-(F (xPart z) ^ 2)⁻¹ * fderiv ℝ F (xPart z) (xPart v)) +
    (F (xPart z))⁻¹ * tPart v =
    (tPart v - (tPart z * (F (xPart z))⁻¹) * fderiv ℝ F (xPart z) (xPart v)) /
      F (xPart z)
  field_simp
  ring

-- @node: normalizedTime_second_relation
/-- Suppose [Ω is open and F and P are smooth and positive on Ω](hyp:hFP) and
[the spatial coordinates x of z lie in Ω](hyp:hz). [F(x) times the second
differential of normalized time q at z along v and w equals −q(z) times the
second differential of F at x along their spatial components, minus the
derivative of F along the spatial component of v times the derivative of q
along w, minus the derivative of q along v times the derivative of F along
the spatial component of w](goal). -/
lemma normalizedTime_second_relation {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) (v w : EuclideanSpace ℝ (Fin (m + 1))) :
    F (xPart z) * secondDifferential (normalizedTime F) z v w =
      -(normalizedTime F z * secondDifferential F (xPart z) (xPart v) (xPart w)) -
        fderiv ℝ F (xPart z) (xPart v) * fderiv ℝ (normalizedTime F) z w -
        fderiv ℝ (normalizedTime F) z v * fderiv ℝ F (xPart z) (xPart w) := by
  have hf : ContDiffAt ℝ 2 F (xPart z) :=
    (hFP.2.1.contDiffAt (hFP.1.mem_nhds hz)).of_le (by decide)
  have hq : ContDiffAt ℝ 2 (normalizedTime F) z :=
    (normalizedTime_contDiffAt hFP hz).of_le (by decide)
  let L := xProjection m
  have hfc : ContDiffAt ℝ 2 (fun y => F (L y)) z := hf.comp z L.contDiff.contDiffAt
  have hF := (hFP.2.2.2 _ hz).1.ne'
  have heq : (fun y => F (L y) * normalizedTime F y) =ᶠ[𝓝 z] tPart := by
    filter_upwards [hfc.continuousAt.eventually_ne hF] with y hy
    change F (xPart y) * (tPart y / F (xPart y)) = tPart y
    change F (xPart y) ≠ 0 at hy
    field_simp
  have he := secondDifferential_congr heq v w
  rw [secondDifferential_mul hfc hq, secondDifferential_comp_clm L hf] at he
  have hd : fderiv ℝ (fun y => F (L y)) z = (fderiv ℝ F (L z)).comp L :=
    ((hf.differentiableAt (by norm_num)).hasFDerivAt.comp z L.hasFDerivAt).fderiv
  rw [hd] at he
  have ht : secondDifferential (@tPart m) z v w = 0 :=
    secondDifferential_clm (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)) z v w
  rw [ht] at he
  change F (xPart z) * secondDifferential (normalizedTime F) z v w +
    normalizedTime F z * secondDifferential F (xPart z) (xPart v) (xPart w) +
    fderiv ℝ F (xPart z) (xPart v) * fderiv ℝ (normalizedTime F) z w +
    fderiv ℝ (normalizedTime F) z v * fderiv ℝ F (xPart z) (xPart w) = 0 at he
  linarith

-- @node: normalizedTime_adapted_deriv
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP),
[the spatial coordinates x of z lie in Ω](hyp:hz), and [F(x) is positive](hyp:hF),
then [the derivative of normalized time at z along the i-th adapted spatial
vector is zero](goal). -/
lemma normalizedTime_adapted_deriv {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) (hF : 0 < F (xPart z)) (i : Fin m) :
    fderiv ℝ (normalizedTime F) z (adaptedSpatialBasis F z hF i) = 0 := by
  rw [normalizedTime_fderiv hFP hz]
  simp [tPart_adaptedSpatialBasis, xPart_adaptedSpatialBasis, normalizedTime]

-- @node: normalizedTime_time_deriv
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP) and
[the spatial coordinates x of z lie in Ω](hyp:hz), then [the derivative of
normalized time at z along the time unit vector equals 1/F(x)](goal). -/
lemma normalizedTime_time_deriv {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) :
    fderiv ℝ (normalizedTime F) z (timeBasis m) = 1 / F (xPart z) := by
  rw [normalizedTime_fderiv hFP hz]
  simp [tPart_timeBasis, xPart_timeBasis]

-- @node: normalizedTime_adapted_second
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP),
[the spatial coordinates x of z lie in Ω](hyp:hz), and [F(x) is positive](hyp:hF),
then [the second differential of normalized time at z along adapted spatial
vectors i and j equals minus normalized time at z divided by F(x), multiplied
by the entry in row i and column j of the Hessian of F at x](goal). -/
lemma normalizedTime_adapted_second {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) (hF : 0 < F (xPart z)) (i j : Fin m) :
    secondDifferential (normalizedTime F) z
      (adaptedSpatialBasis F z hF i) (adaptedSpatialBasis F z hF j) =
      -(normalizedTime F z / F (xPart z)) * hessianMatrix F (xPart z) i j := by
  have h := normalizedTime_second_relation hFP hz
    (adaptedSpatialBasis F z hF i) (adaptedSpatialBasis F z hF j)
  simp only [normalizedTime_adapted_deriv hFP hz, xPart_adaptedSpatialBasis,
    mul_zero, zero_mul, sub_zero] at h
  rw [← hessianMatrix_eq_secondDifferential
    ((hFP.2.1.contDiffAt (hFP.1.mem_nhds hz)).of_le (by decide))] at h
  apply (mul_left_cancel₀ hF.ne')
  field_simp
  linarith

-- @node: normalizedTime_time_second
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP) and
[the spatial coordinates of z lie in Ω](hyp:hz), then [the second differential
of normalized time at z applied twice to the time unit vector is zero](goal). -/
lemma normalizedTime_time_second {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) :
    secondDifferential (normalizedTime F) z (timeBasis m) (timeBasis m) = 0 := by
  have h := normalizedTime_second_relation hFP hz (timeBasis m) (timeBasis m)
  simp only [xPart_timeBasis, secondDifferential, map_zero, mul_zero, zero_mul,
    neg_zero, sub_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (hFP.2.2.2 _ hz).1.ne'

-- @node: spatialLift_secondDifferential
/-- If [f is twice continuously differentiable at the spatial coordinates x
of z](hyp:hf), then [the second differential at z of f evaluated on spatial
coordinates, in directions v and w, equals the second differential of f at x
applied to the spatial components of v and w](goal). -/
lemma spatialLift_secondDifferential {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {z : EuclideanSpace ℝ (Fin (m + 1))} (hf : ContDiffAt ℝ 2 f (xPart z))
    (v w : EuclideanSpace ℝ (Fin (m + 1))) :
    secondDifferential (fun y => f (xPart y)) z v w =
      secondDifferential f (xPart z) (xPart v) (xPart w) :=
  secondDifferential_comp_clm (xProjection m) hf v w

-- @node: spatialLift_fderiv
/-- If [f is differentiable at the spatial coordinates x of z](hyp:hf), then
[the derivative at z of f evaluated on spatial coordinates, along v, equals
the derivative of f at x along the spatial component of v](goal). -/
lemma spatialLift_fderiv {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {z : EuclideanSpace ℝ (Fin (m + 1))} (hf : DifferentiableAt ℝ f (xPart z))
    (v : EuclideanSpace ℝ (Fin (m + 1))) :
    fderiv ℝ (fun y => f (xPart y)) z v = fderiv ℝ f (xPart z) (xPart v) := by
  have hd := hf.hasFDerivAt.comp z (xProjection m).hasFDerivAt
  rw [show fderiv ℝ (fun y => f (xPart y)) z = _ from hd.fderiv]
  rfl

-- @node: scalarLift_fderiv
/-- If [q is differentiable at z](hyp:hq) and [the scalar function h is
differentiable at q(z)](hyp:hh), then [the derivative of h composed with q at z
along v equals h′(q(z)) times the derivative of q at z along v](goal). -/
lemma scalarLift_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : E → ℝ} {h : ℝ → ℝ} {z : E} (hq : DifferentiableAt ℝ q z)
    (hh : DifferentiableAt ℝ h (q z)) (v : E) :
    fderiv ℝ (fun y => h (q y)) z v = deriv h (q z) * fderiv ℝ q z v := by
  have hd := hh.hasDerivAt.comp_hasFDerivAt z hq.hasFDerivAt
  rw [show fderiv ℝ (fun y => h (q y)) z = _ from hd.fderiv]
  rfl

-- @node: normalizedWeight
/-- For [spatial functions F and P](hyp:F,P) and [a point z with spatial
coordinates x and time coordinate t](hyp:z), the [normalized weight](goal)
equals P(x) times the scalar reduction factor evaluated at t/F(x). -/
def normalizedWeight {m : ℕ} (F P : EuclideanSpace ℝ (Fin m) → ℝ)
    (z : EuclideanSpace ℝ (Fin (m + 1))) : ℝ :=
  P (xPart z) * reductionH m (normalizedTime F z)

-- @node: normalizedWeight_contDiffAt
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP) and
[the spatial coordinates of z lie in Ω](hyp:hz), then [the normalized weight
is infinitely differentiable at z](goal). -/
@[fun_prop] lemma normalizedWeight_contDiffAt {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) : ContDiffAt ℝ ∞ (normalizedWeight F P) z := by
  have hp := hFP.2.2.1.contDiffAt (hFP.1.mem_nhds hz)
  have hq := normalizedTime_contDiffAt hFP hz
  unfold normalizedWeight
  fun_prop

-- @node: normalizedWeight_adapted_second
/-- Suppose [Ω is open and F and P are smooth and positive on Ω](hyp:hFP),
[the spatial coordinates x of z lie in Ω](hyp:hz), and [F(x) is positive](hyp:hF).
[The second differential of the normalized weight at z along adapted spatial
vectors i and j equals h(q) times the entry in row i and column j of the
Hessian of P at x, minus (P(x)/F(x)) times q times h′(q) times the corresponding
Hessian entry of F, where q is normalized time at z and h is the scalar
reduction factor](goal). -/
lemma normalizedWeight_adapted_second {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) (hF : 0 < F (xPart z)) (i j : Fin m) :
    secondDifferential (normalizedWeight F P) z
      (adaptedSpatialBasis F z hF i) (adaptedSpatialBasis F z hF j) =
      reductionH m (normalizedTime F z) * hessianMatrix P (xPart z) i j -
        P (xPart z) / F (xPart z) * normalizedTime F z *
          deriv (reductionH m) (normalizedTime F z) * hessianMatrix F (xPart z) i j := by
  have hp : ContDiffAt ℝ 2 P (xPart z) :=
    (hFP.2.2.1.contDiffAt (hFP.1.mem_nhds hz)).of_le (by decide)
  have hpC : ContDiffAt ℝ 2 (fun y => P (xPart y)) z :=
    hp.comp z (xProjection m).contDiff.contDiffAt
  have hq : ContDiffAt ℝ 2 (normalizedTime F) z :=
    (normalizedTime_contDiffAt hFP hz).of_le (by decide)
  have hh : ContDiff ℝ 2 (reductionH m) := (reductionH_contDiff m).of_le (by decide)
  have hhC : ContDiffAt ℝ 2 (fun y => reductionH m (normalizedTime F y)) z :=
    hh.contDiffAt.comp z hq
  unfold normalizedWeight
  rw [secondDifferential_mul hpC hhC, secondDifferential_scalar_comp hq hh,
    spatialLift_secondDifferential hp]
  simp only [scalarLift_fderiv (hq.differentiableAt (by norm_num))
      (hh.differentiable (by norm_num) _), normalizedTime_adapted_deriv hFP hz,
    normalizedTime_adapted_second hFP hz, xPart_adaptedSpatialBasis,
    mul_zero, zero_mul, add_zero]
  rw [← hessianMatrix_eq_secondDifferential hp]
  field_simp
  ring

-- @node: normalizedWeight_time_second
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP) and
[the spatial coordinates x of z lie in Ω](hyp:hz), then [the second
differential of the normalized weight at z applied twice to the time unit
vector equals P(x)/F(x)² times the second derivative of the scalar reduction
factor evaluated at normalized time at z](goal). -/
lemma normalizedWeight_time_second {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) :
    secondDifferential (normalizedWeight F P) z (timeBasis m) (timeBasis m) =
      P (xPart z) / F (xPart z) ^ 2 * deriv (deriv (reductionH m)) (normalizedTime F z) := by
  have hp : ContDiffAt ℝ 2 P (xPart z) :=
    (hFP.2.2.1.contDiffAt (hFP.1.mem_nhds hz)).of_le (by decide)
  have hpC : ContDiffAt ℝ 2 (fun y => P (xPart y)) z :=
    hp.comp z (xProjection m).contDiff.contDiffAt
  have hq : ContDiffAt ℝ 2 (normalizedTime F) z :=
    (normalizedTime_contDiffAt hFP hz).of_le (by decide)
  have hh : ContDiff ℝ 2 (reductionH m) := (reductionH_contDiff m).of_le (by decide)
  have hhC : ContDiffAt ℝ 2 (fun y => reductionH m (normalizedTime F y)) z :=
    hh.contDiffAt.comp z hq
  unfold normalizedWeight
  rw [secondDifferential_mul hpC hhC, secondDifferential_scalar_comp hq hh,
    spatialLift_secondDifferential hp, normalizedTime_time_second hFP hz]
  simp only [spatialLift_fderiv (hp.differentiableAt (by norm_num)),
    normalizedTime_time_deriv hFP hz,
    xPart_timeBasis, secondDifferential, map_zero, mul_zero, zero_mul, add_zero, zero_add]
  ring

end OaiSmoothNonquadraticAffine
