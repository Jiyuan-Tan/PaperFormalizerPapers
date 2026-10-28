module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.ReductionMatrix

/-! # The dimension-independent square-root reduction -/

public section

noncomputable section

open Set Matrix Filter
open scoped ContDiff BigOperators Topology

namespace OaiSmoothNonquadraticAffine

-- @node: spatialTimeBlock_mul
/-- [Multiplying block diagonal matrices with spatial blocks A and B and time
entries d and e gives the block diagonal matrix with spatial block AB and time
entry de](goal). -/
lemma spatialTimeBlock_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (d e : ℝ) :
    spatialTimeBlock A d * spatialTimeBlock B e = spatialTimeBlock (A * B) (d * e) := by
  ext i j
  refine Fin.lastCases ?_ (fun a => ?_) i <;>
    refine Fin.lastCases ?_ (fun b => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, spatialTimeBlock]

-- @node: spatialTimeBlock_one
/-- In every spatial dimension m, [the block diagonal matrix with the spatial
identity and time entry one is the full identity matrix](goal). -/
lemma spatialTimeBlock_one (m : ℕ) :
    spatialTimeBlock (1 : Matrix (Fin m) (Fin m) ℝ) 1 = 1 := by
  ext i j
  refine Fin.lastCases ?_ (fun a => ?_) i <;>
    refine Fin.lastCases ?_ (fun b => ?_) j <;>
    simp [spatialTimeBlock, Matrix.one_apply, eq_comm]

-- @node: spatialTimeBlock_inv
/-- If [A has nonzero determinant](hyp:hA) and [d is nonzero](hyp:hd), [the
inverse of the block diagonal matrix with spatial block A and time entry d has
spatial block A⁻¹ and time entry d⁻¹](goal). -/
lemma spatialTimeBlock_inv {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (d : ℝ)
    (hA : IsUnit A.det) (hd : d ≠ 0) :
    (spatialTimeBlock A d)⁻¹ = spatialTimeBlock A⁻¹ d⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [spatialTimeBlock_mul, Matrix.nonsing_inv_mul _ hA, inv_mul_cancel₀ hd,
    spatialTimeBlock_one]

-- @node: spatialTimeBlock_trace_mul
/-- [The trace of the block diagonal matrix with spatial block A and time
entry d multiplied by W equals the trace of A times the spatial submatrix of W,
plus d times the final diagonal entry of W](goal). -/
lemma spatialTimeBlock_trace_mul {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (d : ℝ)
    (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    Matrix.trace (spatialTimeBlock A d * W) =
      Matrix.trace (A * W.submatrix Fin.castSucc Fin.castSucc) +
        d * W (Fin.last m) (Fin.last m) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_castSucc, spatialTimeBlock]

-- @node: trace_inverse_congruence
/-- If [M has nonzero determinant](hyp:hM), [transforming both H and W by
multiplication on the left by the transpose of M and on the right by M preserves
the trace of the inverse of the first matrix times the second](goal). -/
lemma trace_inverse_congruence {n : ℕ} (H W M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsUnit M.det) :
    Matrix.trace ((Mᵀ * H * M)⁻¹ * (Mᵀ * W * M)) = Matrix.trace (H⁻¹ * W) := by
  have hMt : IsUnit Mᵀ.det := by simpa using hM
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  calc
    _ = Matrix.trace (M⁻¹ * (H⁻¹ * ((Mᵀ)⁻¹ * Mᵀ) * W) * M) := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (M⁻¹ * (H⁻¹ * W) * M) := by
      rw [Matrix.nonsing_inv_mul _ hMt, Matrix.mul_one]
    _ = Matrix.trace (M * M⁻¹ * (H⁻¹ * W)) := Matrix.trace_mul_cycle _ _ _
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hM, Matrix.one_mul]

-- @node: matrix_inv_smul_real
/-- If [A has nonzero determinant](hyp:hA) and [the real scalar c is nonzero](hyp:hc),
[the inverse of c times A equals c⁻¹ times A⁻¹](goal). -/
lemma matrix_inv_smul_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hA : IsUnit A.det) (hc : c ≠ 0) : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hA,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

-- @node: normalizedWeight_congruence_spatial
/-- Suppose [Ω is open and F and P are smooth and positive on Ω](hyp:hFP),
[the spatial coordinates x of z belong to Ω](hyp:hz), and [F(x) is positive](hyp:hF).
[The spatial block of the normalized weight's Hessian in the adapted frame at z
equals h(q) times the Hessian of P at x minus (P(x)/F(x))qh′(q) times the Hessian
of F at x, where q is time divided by F(x) and h(q) = (1 + q²) raised to (m + 2)/2](goal). -/
lemma normalizedWeight_congruence_spatial {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) (hF : 0 < F (xPart z)) :
    ((adaptedFrameMatrix F z hF)ᵀ * hessianMatrix (normalizedWeight F P) z *
      adaptedFrameMatrix F z hF).submatrix Fin.castSucc Fin.castSucc =
      reductionH m (normalizedTime F z) • hessianMatrix P (xPart z) -
        (P (xPart z) / F (xPart z) * normalizedTime F z *
          deriv (reductionH m) (normalizedTime F z)) • hessianMatrix F (xPart z) := by
  have hw : ContDiffAt ℝ 2 (normalizedWeight F P) z :=
    (normalizedWeight_contDiffAt hFP hz).of_le (by decide)
  ext i j
  rw [Matrix.submatrix_apply, hessian_congruence_entry hw]
  change secondDifferential (normalizedWeight F P) z
    (adaptedFrame F z hF i.castSucc) (adaptedFrame F z hF j.castSucc) = _
  simpa [adaptedFrame] using normalizedWeight_adapted_second hFP hz hF i j

-- @node: normalizedWeight_congruence_time
/-- Suppose [Ω is open and F and P are smooth and positive on Ω](hyp:hFP),
[the spatial coordinates x of z belong to Ω](hyp:hz), and [F(x) is positive](hyp:hF).
[The final diagonal entry of the normalized weight's Hessian in the adapted frame
at z equals P(x)h″(q)/F(x)², where q is time divided by F(x) and
h(q) = (1 + q²) raised to (m + 2)/2](goal). -/
lemma normalizedWeight_congruence_time {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : xPart z ∈ Ω) (hF : 0 < F (xPart z)) :
    ((adaptedFrameMatrix F z hF)ᵀ * hessianMatrix (normalizedWeight F P) z *
      adaptedFrameMatrix F z hF) (Fin.last m) (Fin.last m) =
      P (xPart z) / F (xPart z) ^ 2 * deriv (deriv (reductionH m)) (normalizedTime F z) := by
  have hw : ContDiffAt ℝ 2 (normalizedWeight F P) z :=
    (normalizedWeight_contDiffAt hFP hz).of_le (by decide)
  rw [hessian_congruence_entry hw]
  change secondDifferential (normalizedWeight F P) z
    (adaptedFrame F z hF (Fin.last m)) (adaptedFrame F z hF (Fin.last m)) = _
  simpa [adaptedFrame] using normalizedWeight_time_second hFP hz

-- @node: reductionGraph_trace_identity
/-- Suppose [Ω is open and F and P are smooth and positive on Ω](hyp:hFP),
[the Hessian of F is positive definite throughout Ω](hyp:hH), and [the spatial
coordinates x of z lie in Ω](hyp:hz). Then [F(x)/u(z) times the trace of the inverse
Hessian of the reduction graph u times the Hessian of the normalized weight equals
h(q) times the spatial trace tr((Hess F)⁻¹ Hess P) plus
(P(x)/F(x))((1 + q²)h″(q) − mqh′(q)), where all full Hessians are at z, all spatial
Hessians are at x, q is time divided by F(x), and h(q) = (1 + q²) raised to (m + 2)/2](goal). -/
lemma reductionGraph_trace_identity {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) (hH : ReductionHessianPosDef Ω F)
    {z : EuclideanSpace ℝ (Fin (m + 1))} (hz : xPart z ∈ Ω) :
    F (xPart z) / reductionGraph F z *
      Matrix.trace ((hessianMatrix (reductionGraph F) z)⁻¹ *
        hessianMatrix (normalizedWeight F P) z) =
    reductionH m (normalizedTime F z) *
        Matrix.trace ((hessianMatrix F (xPart z))⁻¹ * hessianMatrix P (xPart z)) +
      P (xPart z) / F (xPart z) *
        ((1 + normalizedTime F z ^ 2) * deriv (deriv (reductionH m)) (normalizedTime F z) -
          (m : ℝ) * normalizedTime F z * deriv (reductionH m) (normalizedTime F z)) := by
  have hF := (hFP.2.2.2 _ hz).1
  have hu : 0 < reductionGraph F z := by unfold reductionGraph; positivity
  have hA : IsUnit (hessianMatrix F (xPart z)).det := isUnit_iff_ne_zero.mpr (hH _ hz).det_pos.ne'
  have hc : F (xPart z) / reductionGraph F z ≠ 0 := (div_pos hF hu).ne'
  have hd : F (xPart z) ^ 2 / reductionGraph F z ^ 3 ≠ 0 := by positivity
  have hCA : IsUnit ((F (xPart z) / reductionGraph F z) • hessianMatrix F (xPart z)).det := by
    rw [Matrix.det_smul]
    exact IsUnit.mul (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hc)) hA
  have hM : IsUnit (adaptedFrameMatrix F z hF).det := by
    rw [adaptedFrameMatrix_det]
    exact isUnit_one
  rw [← trace_inverse_congruence _ _ (adaptedFrameMatrix F z hF) hM,
    reductionGraph_hessian_congruence hFP hz hF, spatialTimeBlock_inv _ _ hCA hd,
    spatialTimeBlock_trace_mul, normalizedWeight_congruence_spatial hFP hz hF,
    normalizedWeight_congruence_time hFP hz hF, matrix_inv_smul_real _ _ hA hc,
    Matrix.smul_mul, Matrix.trace_smul, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.nonsing_inv_mul _ hA, Matrix.trace_one, Fintype.card_fin]
  have husq : reductionGraph F z ^ 2 = F (xPart z) ^ 2 + tPart z ^ 2 :=
    Real.sq_sqrt (by positivity)
  unfold normalizedTime
  simp only [smul_eq_mul]
  field_simp [hF.ne', hu.ne']
  linear_combination P (xPart z) * deriv (deriv (reductionH m))
    (tPart z / F (xPart z)) * husq

-- @node: affineWeight_eventuallyEq_normalizedWeight
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP),
[F and P satisfy the reduced determinant and trace equations on Ω](hyp:hSystem),
and [the spatial coordinates of z lie in Ω](hyp:hz), [the affine weight of the
square-root reduction graph agrees with the normalized weight on a neighborhood of z](goal). -/
lemma affineWeight_eventuallyEq_normalizedWeight {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) (hSystem : ReducedSystem m Ω F P)
    {z : EuclideanSpace ℝ (Fin (m + 1))} (hz : xPart z ∈ Ω) :
    affineWeight (m + 1) (reductionGraph F) =ᶠ[𝓝 z] normalizedWeight F P := by
  have he : ∀ᶠ y in 𝓝 z, xPart y ∈ Ω :=
    (xProjection m).continuous.continuousAt.eventually (hFP.1.mem_nhds hz)
  filter_upwards [he] with y hy
  exact reduction_affineWeight_eq hFP hSystem hy

-- @node: hessianMatrix_congr
/-- If [f and g agree on a neighborhood of z](hyp:heq), [their Hessian matrices
at z are equal](goal). -/
lemma hessianMatrix_congr {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {z : EuclideanSpace ℝ (Fin n)} (heq : f =ᶠ[𝓝 z] g) :
    hessianMatrix f z = hessianMatrix g z := by
  ext i j
  have he : (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ g y (EuclideanSpace.single j 1)) :=
    (heq.fderiv (𝕜 := ℝ)).mono fun _ h => congrArg (fun L => L (EuclideanSpace.single j 1)) h
  exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
    L (EuclideanSpace.single i 1)) he.fderiv_eq

-- @node: reductionGraph_trace_zero
/-- Suppose [Ω is open and F and P are smooth and positive on Ω](hyp:hFP),
[the Hessian of F is positive definite throughout Ω](hyp:hH), [F and P satisfy
the reduced determinant and trace equations on Ω](hyp:hSystem), and [the spatial
coordinates of z lie in Ω](hyp:hz). Then [the trace of the inverse Hessian of the
square-root reduction graph times the Hessian of its affine weight is zero at z](goal). -/
lemma reductionGraph_trace_zero {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) (hH : ReductionHessianPosDef Ω F)
    (hSystem : ReducedSystem m Ω F P)
    {z : EuclideanSpace ℝ (Fin (m + 1))} (hz : xPart z ∈ Ω) :
    Matrix.trace ((hessianMatrix (reductionGraph F) z)⁻¹ *
      hessianMatrix (affineWeight (m + 1) (reductionGraph F)) z) = 0 := by
  rw [hessianMatrix_congr (affineWeight_eventuallyEq_normalizedWeight hFP hSystem hz)]
  have h := reductionGraph_trace_identity hFP hH hz
  rw [reduction_trace_vanishes hSystem hz (normalizedTime F z)] at h
  have hF := (hFP.2.2.2 _ hz).1
  have hu : 0 < reductionGraph F z := by unfold reductionGraph; positivity
  exact (mul_eq_zero.mp h).resolve_left (div_pos hF hu).ne'

-- @node: matrix_cofactor_contraction
/-- If [H is positive definite](hyp:hH) and [W is a symmetric real matrix](hyp:hW),
[the sum of the entrywise products of the adjugate of H and W equals the determinant
of H times the trace of H⁻¹W](goal). -/
lemma matrix_cofactor_contraction {n : ℕ} (H W : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hW : W.IsHermitian) :
    (∑ i, ∑ j, H.adjugate i j * W i j) = H.det * Matrix.trace (H⁻¹ * W) := by
  have hadj : H.det • H⁻¹ = H.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hH.det_pos.ne', one_smul]
  calc
    _ = Matrix.trace (H.adjugate * W) := by
      simp only [Matrix.trace]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun a : ℝ => H.adjugate i j * a)
        (by simpa only [star_trivial] using (hW.apply i j).symm)
    _ = _ := by rw [← hadj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

-- @node: reductionGraph_affineMaximalEquation
/-- If [Ω is open and F and P are smooth and positive on Ω](hyp:hFP),
[the Hessian of F is positive definite throughout Ω](hyp:hH), and [F and P satisfy
the reduced determinant and trace equations on Ω](hyp:hSystem), [the square-root
reduction graph satisfies the affine maximal equation at every point whose
spatial coordinates belong to Ω](goal). -/
lemma reductionGraph_affineMaximalEquation {m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin m))} {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hFP : ReductionFunctions Ω F P) (hH : ReductionHessianPosDef Ω F)
    (hSystem : ReducedSystem m Ω F P) :
    AffineMaximalEquation (m + 1) (reductionGraph F) {z | xPart z ∈ Ω} := by
  intro z hz
  have hweight := hessianMatrix_congr (affineWeight_eventuallyEq_normalizedWeight hFP hSystem hz)
  have hw : (hessianMatrix (affineWeight (m + 1) (reductionGraph F)) z).IsHermitian := by
    rw [hweight]
    exact hessianMatrix_isHermitian ((normalizedWeight_contDiffAt hFP hz).of_le (by decide))
  change (∑ i, ∑ j, (hessianMatrix (reductionGraph F) z).adjugate i j *
    hessianMatrix (affineWeight (m + 1) (reductionGraph F)) z i j) = 0
  rw [matrix_cofactor_contraction _ _ (reductionGraph_hessianPositive hFP hH z hz) hw,
    reductionGraph_trace_zero hFP hH hSystem hz, mul_zero]

-- @node: prop:reduction
/-- If [the spatial dimension m is at least one](hyp:hm), [Ω is open and F and P
are smooth and positive on Ω](hyp:hFP), [the Hessian of F is positive definite
throughout Ω](hyp:hH), and [F and P satisfy the reduced determinant and trace
equations on Ω](hyp:hSystem), [the square-root reduction graph in dimension m + 1
has a positive definite Hessian and satisfies the affine maximal equation
at every point whose spatial coordinates belong to Ω](goal). -/
theorem reduction_affineMaximal {m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin m))}
    {F P : EuclideanSpace ℝ (Fin m) → ℝ}
    (hm : ReductionDimension m) (hFP : ReductionFunctions Ω F P)
    (hH : ReductionHessianPosDef Ω F) (hSystem : ReducedSystem m Ω F P) :
    HessianPositive (reductionGraph F) {z | xPart z ∈ Ω} ∧
      AffineMaximalEquation (m + 1) (reductionGraph F) {z | xPart z ∈ Ω} := by
  exact ⟨reductionGraph_hessianPositive hFP hH,
    reductionGraph_affineMaximalEquation hFP hH hSystem⟩

end OaiSmoothNonquadraticAffine
