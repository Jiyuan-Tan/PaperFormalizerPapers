module

public import Papers.OaiSmoothNonquadraticAffine.TReduction
public import Papers.OaiSmoothNonquadraticAffine.TGlobal
public import Papers.OaiSmoothNonquadraticAffine.Helpers.Local
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # A smooth nonquadratic entire affine maximal graph in ten dimensions -/

public section

open Set Filter Matrix
open scoped BigOperators ContDiff Topology RealInnerProductSpace

namespace OaiSmoothNonquadraticAffine

-- @node: norm_fderiv_apply_real
/-- At [a nonzero point x](hyp:hx), [the directional derivative of the Euclidean
norm along any vector v equals the inner product of x and v divided by the norm of x](goal). -/
lemma norm_fderiv_apply_real {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ≠ 0) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) x v = ⟪x, v⟫ / ‖x‖ := by
  have hn : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) x := by
    exact differentiableAt_id.norm ℝ hx
  have hd := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v)
    (fderiv_norm_sq_apply x)
  rw [fderiv_fun_pow 2 hn] at hd
  simp only [_root_.smul_apply, smul_eq_mul, innerSL_apply_apply] at hd
  simp only [Nat.reduceSub, pow_one, nsmul_eq_mul] at hd
  apply (eq_div_iff (norm_ne_zero_iff.mpr hx)).2
  norm_num at hd
  nlinarith [hd]

-- @node: radialExtension_fderiv_apply
/-- If [x is nonzero](hyp:hx) and [f is differentiable at the norm of x](hyp:hf),
[the directional derivative of its radial extension along v equals f′ at that
radius, divided by the radius, times the inner product of x and v](goal). -/
lemma radialExtension_fderiv_apply {n : ℕ} {f : ℝ → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (hf : DifferentiableAt ℝ f ‖x‖) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (radialExtension n f) x v = deriv f ‖x‖ / ‖x‖ * ⟪x, v⟫ := by
  have hn : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) x := by
    exact differentiableAt_id.norm ℝ hx
  change fderiv ℝ (f ∘ (fun y => ‖y‖)) x v = _
  rw [fderiv_comp x hf hn, ContinuousLinearMap.comp_apply,
    fderiv_eq_deriv_mul, norm_fderiv_apply_real hx]
  ring

-- @node: radialExtension_hessian
/-- If [x is nonzero](hyp:hx) and [f is twice continuously differentiable at
the radius r equal to the norm of x](hyp:hf), [the Hessian of its radial extension
at x equals (f′(r)/r) times the identity plus ((f″(r) − f′(r)/r)/r²) times the
outer product of x with itself](goal). -/
lemma radialExtension_hessian {n : ℕ} {f : ℝ → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) (hf : ContDiffAt ℝ 2 f ‖x‖) :
    hessianMatrix (radialExtension n f) x =
      (deriv f ‖x‖ / ‖x‖) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      ((deriv (deriv f) ‖x‖ - deriv f ‖x‖ / ‖x‖) / ‖x‖ ^ 2) •
        Matrix.vecMulVec (fun i => x i) (fun i => x i) := by
  have hn : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) x := by
    exact contDiffAt_id.norm ℝ hx
  have hdf : DifferentiableAt ℝ (deriv f) ‖x‖ :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt_one
  have heq (j : Fin n) :
      (fun y => fderiv ℝ (radialExtension n f) y (EuclideanSpace.single j 1)) =ᶠ[𝓝 x]
      (fun y => deriv f ‖y‖ / ‖y‖ * y j) := by
    have hnear := continuous_norm.continuousAt.eventually (hf.eventually (by norm_num))
    filter_upwards [hnear, eventually_ne_nhds hx] with y hy hy0
    rw [radialExtension_fderiv_apply hy0 (hy.differentiableAt (by norm_num))]
    simp [EuclideanSpace.inner_single_right]
  ext i j
  change fderiv ℝ (fun y => fderiv ℝ (radialExtension n f) y
    (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) = _
  rw [(heq j).fderiv_eq]
  have hdn := (hn.differentiableAt (by norm_num)).hasFDerivAt
  have hdq := ((hdf.hasDerivAt.comp_hasFDerivAt x hdn).mul
    (((hasDerivAt_id ‖x‖).inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x hdn)).mul
      (EuclideanSpace.proj j).hasFDerivAt
  simp only [div_eq_mul_inv] at *
  change HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) =>
    deriv f ‖y‖ * ‖y‖⁻¹ * y j) _ x at hdq
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  rw [hdq.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    norm_fderiv_apply_real hx, Function.comp_apply, Pi.mul_apply, Pi.inv_apply, id_eq,
    EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul,
    EuclideanSpace.coe_proj, PiLp.single_apply]
  change deriv f ‖x‖ * ‖x‖⁻¹ * (if j = i then 1 else 0) +
    x j * (deriv f ‖x‖ * (-1 * (‖x‖ ^ 2)⁻¹ * (x i / ‖x‖)) +
      ‖x‖⁻¹ * (deriv (deriv f) ‖x‖ * (x i / ‖x‖))) = _
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    field_simp [norm_ne_zero_iff.mpr hx]
    ring
  · simp only [hij, Ne.symm hij, ite_false, mul_zero, zero_add]
    field_simp [norm_ne_zero_iff.mpr hx]
    ring

-- @node: scalar_add_rankOne_det
/-- If [a is nonzero](hyp:ha), [the determinant of a times the n-dimensional
identity plus b times the outer product of v with itself equals aⁿ times
(1 + (b/a) times the squared Euclidean length of v)](goal). -/
lemma scalar_add_rankOne_det {n : ℕ} (v : Fin n → ℝ) (a b : ℝ) (ha : a ≠ 0) :
    (a • (1 : Matrix (Fin n) (Fin n) ℝ) + b • vecMulVec v v).det =
      a ^ n * (1 + b / a * (v ⬝ᵥ v)) := by
  have heq : a • (1 : Matrix (Fin n) (Fin n) ℝ) + b • vecMulVec v v =
      a • (1 + Matrix.replicateCol Unit ((b / a) • v) * Matrix.replicateRow Unit v) := by
    rw [← Matrix.vecMulVec_eq]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul]
    field_simp [ha]
  rw [heq, Matrix.det_smul, Fintype.card_fin,
    Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul]

-- @node: rankOne_eigen_inverse
/-- If [r is nonzero](hyp:hr), [a is nonzero](hyp:ha), [b is nonzero](hyp:hb),
and [the squared length of v is r²](hyp:hv), [the inverse of a times the identity
plus ((b − a)/r²) times the outer product of v with itself equals a⁻¹ times the
identity plus ((b⁻¹ − a⁻¹)/r²) times that outer product](goal). -/
lemma rankOne_eigen_inverse {n : ℕ} (v : Fin n → ℝ) (r a b : ℝ)
    (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hv : v ⬝ᵥ v = r ^ 2) :
    (a • (1 : Matrix (Fin n) (Fin n) ℝ) + ((b - a) / r ^ 2) • vecMulVec v v)⁻¹ =
      a⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) +
        ((b⁻¹ - a⁻¹) / r ^ 2) • vecMulVec v v := by
  apply Matrix.inv_eq_left_inv
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.vecMulVec_mul_vecMulVec, hv,
    Matrix.vecMulVec_smul, smul_smul, smul_add]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Matrix.one_apply]
  split_ifs <;> field_simp [ha, hb, hr] <;> ring

-- @node: rankOne_eigen_trace
/-- If [r is nonzero](hyp:hr), [a is nonzero](hyp:ha), [b is nonzero](hyp:hb),
and [the squared length of v is r²](hyp:hv), [the trace of the inverse of
aI + ((b − a)/r²)vvᵀ multiplied by cI + ((d − c)/r²)vvᵀ equals
(n − 1)c/a + d/b, where I is the n-dimensional identity](goal). -/
lemma rankOne_eigen_trace {n : ℕ} (v : Fin n → ℝ) (r a b c d : ℝ)
    (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hv : v ⬝ᵥ v = r ^ 2) :
    Matrix.trace
      ((a • (1 : Matrix (Fin n) (Fin n) ℝ) + ((b - a) / r ^ 2) • vecMulVec v v)⁻¹ *
        (c • (1 : Matrix (Fin n) (Fin n) ℝ) + ((d - c) / r ^ 2) • vecMulVec v v)) =
      ((n : ℝ) - 1) * c / a + d / b := by
  rw [rankOne_eigen_inverse v r a b hr ha hb hv]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    Matrix.trace_vecMulVec, dotProduct_smul, smul_eq_mul, hv]
  field_simp [hr, ha, hb]
  ring

-- @node: euclidean_dot_self
/-- For every Euclidean vector x, [the sum of its squared coordinates equals
the square of its Euclidean norm](goal). -/
lemma euclidean_dot_self {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    (fun i => x i) ⬝ᵥ (fun i => x i) = ‖x‖ ^ 2 := by
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dotProduct, mul_comm]
    using real_inner_self_eq_norm_sq x

-- @node: radialExtension_det
/-- If [x is nonzero](hyp:hx), [f is twice continuously differentiable at
r equal to the norm of x](hyp:hf), and [f′(r) is nonzero](hyp:hy), [the Hessian
determinant of its nine-dimensional radial extension at x equals f′(r)⁸f″(r)/r⁸](goal). -/
lemma radialExtension_det {f : ℝ → ℝ} {x : EuclideanSpace ℝ (Fin 9)}
    (hx : x ≠ 0) (hf : ContDiffAt ℝ 2 f ‖x‖) (hy : deriv f ‖x‖ ≠ 0) :
    (hessianMatrix (radialExtension 9 f) x).det =
      deriv f ‖x‖ ^ 8 * deriv (deriv f) ‖x‖ / ‖x‖ ^ 8 := by
  rw [radialExtension_hessian hx hf,
    scalar_add_rankOne_det _ _ _ (div_ne_zero hy (norm_ne_zero_iff.mpr hx)),
    euclidean_dot_self]
  field_simp [hy, norm_ne_zero_iff.mpr hx]
  ring

-- @node: radialExtension_trace
/-- If [x is nonzero](hyp:hx), [f is twice continuously differentiable at
r equal to the norm of x](hyp:hf), [p is twice continuously differentiable
there](hyp:hp), [f′(r) is nonzero](hyp:hy), and [f″(r) is nonzero](hyp:hyy),
[the trace of the inverse Hessian of the nine-dimensional radial extension of f
times the Hessian of the radial extension of p equals p″(r)/f″(r) + 8p′(r)/f′(r)](goal). -/
lemma radialExtension_trace {f p : ℝ → ℝ} {x : EuclideanSpace ℝ (Fin 9)}
    (hx : x ≠ 0) (hf : ContDiffAt ℝ 2 f ‖x‖) (hp : ContDiffAt ℝ 2 p ‖x‖)
    (hy : deriv f ‖x‖ ≠ 0) (hyy : deriv (deriv f) ‖x‖ ≠ 0) :
    Matrix.trace ((hessianMatrix (radialExtension 9 f) x)⁻¹ *
      hessianMatrix (radialExtension 9 p) x) =
      deriv (deriv p) ‖x‖ / deriv (deriv f) ‖x‖ + 8 * deriv p ‖x‖ / deriv f ‖x‖ := by
  rw [radialExtension_hessian hx hf, radialExtension_hessian hx hp,
    rankOne_eigen_trace _ ‖x‖ _ _ _ _ (norm_ne_zero_iff.mpr hx)
      (div_ne_zero hy (norm_ne_zero_iff.mpr hx)) hyy (euclidean_dot_self x)]
  norm_num
  field_simp [hy, norm_ne_zero_iff.mpr hx, hyy]
  ring

-- @node: radialSystem_trace_equation
/-- Suppose [F and P satisfy the radial system with dimension nine, coefficient
eleven, and exponent 12/11 at all positive radii](hyp:hs). At [a positive radius r](hyp:hr)
where [F(r) is positive](hyp:hF), [P(r) is positive](hyp:hP), [F′(r) is positive](hyp:hy),
and [F″(r) is positive](hyp:hyy), [P″(r)/F″(r) + 8P′(r)/F′(r) + 11P(r)/F(r) equals zero](goal). -/
lemma radialSystem_trace_equation {F P : ℝ → ℝ}
    (hs : RadialSystem radialDim radialK radialGamma F P (Ioi 0))
    {r : ℝ} (hr : 0 < r) (hF : 0 < F r) (hP : 0 < P r)
    (hy : 0 < deriv F r) (hyy : 0 < deriv (deriv F) r) :
    deriv (deriv P) r / deriv (deriv F) r + 8 * deriv P r / deriv F r +
      11 * P r / F r = 0 := by
  have h := hs r hr
  have hdy := ((h.1.derivWithin (m := 1) (by norm_num)).differentiableAt_one).hasDerivAt
  have hdz := ((h.2.1.derivWithin (m := 1) (by norm_num)).differentiableAt_one).hasDerivAt
  have hflux := ((hdy.pow 8).mul hdz).deriv
  have hdet := h.2.2.1
  have heq := h.2.2.2
  dsimp [radialDim, radialK] at hdet heq
  simp only [Pi.pow_apply] at hflux
  change deriv (fun s => deriv F s ^ 8 * deriv P s) r = _ at hflux
  rw [hflux] at heq
  have hpow : P r ^ (1 - radialGamma) = P r * P r ^ (-radialGamma) := by
    rw [sub_eq_add_neg, Real.rpow_add hP, Real.rpow_one]
  rw [hpow] at heq
  norm_num at heq
  have hpoly : deriv F r ^ 7 *
      (F r * deriv F r * deriv (deriv P) r +
        8 * F r * deriv (deriv F) r * deriv P r +
        11 * P r * deriv F r * deriv (deriv F) r) = 0 := by
    linear_combination F r * heq + 11 * P r * hdet
  have hz := (mul_eq_zero.mp hpoly).resolve_left (pow_ne_zero 7 hy.ne')
  field_simp [hF.ne', hy.ne', hyy.ne']
  nlinarith [hz]

-- @node: radialSystem_reduced_away_zero
/-- If [F and P satisfy the radial system with dimension nine, coefficient eleven,
and exponent 12/11 at all positive radii](hyp:hs), [F, P, F′, and F″ are positive
at every positive radius](hyp:hpos), and [x is nonzero](hyp:hx), [their nine-dimensional
radial extensions satisfy both the Hessian determinant identity det Hess F = F times P raised to −12/11
and the trace identity tr((Hess F)⁻¹ Hess P) + 11P/F = 0 at x](goal). -/
lemma radialSystem_reduced_away_zero {F P : ℝ → ℝ}
    (hs : RadialSystem radialDim radialK radialGamma F P (Ioi 0))
    (hpos : ∀ r > 0, 0 < F r ∧ 0 < P r ∧ 0 < deriv F r ∧ 0 < deriv (deriv F) r)
    {x : EuclideanSpace ℝ (Fin 9)} (hx : x ≠ 0) :
    (hessianMatrix (radialExtension 9 F) x).det =
        radialExtension 9 F x * radialExtension 9 P x ^ (-reductionGamma 9) ∧
      Matrix.trace ((hessianMatrix (radialExtension 9 F) x)⁻¹ *
        hessianMatrix (radialExtension 9 P) x) +
        reductionK 9 * radialExtension 9 P x / radialExtension 9 F x = 0 := by
  have hr := norm_pos_iff.mpr hx
  have h := hs ‖x‖ hr
  have hp := hpos ‖x‖ hr
  constructor
  · rw [radialExtension_det hx h.1 hp.2.2.1.ne']
    have hd := h.2.2.1
    dsimp [radialDim] at hd
    rw [hd]
    norm_num [radialExtension, reductionGamma, radialGamma]
    field_simp [hr.ne']
  · rw [radialExtension_trace hx h.1 h.2.1 hp.2.2.1.ne' hp.2.2.2.ne']
    convert radialSystem_trace_equation hs hr hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 using 1
    norm_num [reductionK, radialExtension]

-- @node: radialExtension_eventuallyEq_at_zero
/-- If [ε is positive](hyp:hε) and [F and G agree at every radius from zero
inclusive to ε exclusive](hyp:heq), [their nine-dimensional radial extensions
agree on a neighborhood of the origin](goal). -/
lemma radialExtension_eventuallyEq_at_zero {ε : ℝ} {F G : ℝ → ℝ}
    (hε : 0 < ε) (heq : ∀ r ∈ Ico 0 ε, F r = G r) :
    radialExtension 9 F =ᶠ[𝓝 0] radialExtension 9 G := by
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 9)) hε] with x hx
  exact heq ‖x‖ ⟨norm_nonneg _, by simpa using hx⟩

-- @node: radialSystem_reduced_everywhere
/-- Suppose [F₀ and P₀ satisfy the local solution conditions with radius ε](hyp:hl),
[F and P agree with F₀ and P₀ respectively from radius zero inclusive to ε exclusive](hyp:heq),
[F and P satisfy the radial system with dimension nine, coefficient eleven, and
exponent 12/11 at all positive radii](hyp:hs), and [F, P, F′, and F″ are positive
at every positive radius](hyp:hpos). Then [their nine-dimensional radial extensions
satisfy det Hess F = F times P raised to −12/11 and
tr((Hess F)⁻¹ Hess P) + 11P/F = 0 everywhere](goal). -/
lemma radialSystem_reduced_everywhere {ε : ℝ} {F₀ P₀ F P : ℝ → ℝ}
    (hl : LocalSolutionData ε F₀ P₀)
    (heq : ∀ r ∈ Ico 0 ε, F r = F₀ r ∧ P r = P₀ r)
    (hs : RadialSystem radialDim radialK radialGamma F P (Ioi 0))
    (hpos : ∀ r > 0, 0 < F r ∧ 0 < P r ∧ 0 < deriv F r ∧ 0 < deriv (deriv F) r) :
    ReducedSystem 9 univ (radialExtension 9 F) (radialExtension 9 P) := by
  intro x _
  by_cases hx : x = 0
  · subst x
    have heF := radialExtension_eventuallyEq_at_zero hl.1 (fun r hr => (heq r hr).1)
    have heP := radialExtension_eventuallyEq_at_zero hl.1 (fun r hr => (heq r hr).2)
    rw [hessianMatrix_congr heF, hessianMatrix_congr heP,
      hl.2.2.2.2.2.2.1, hl.2.2.2.2.2.2.2.1]
    have h0 := heq 0 ⟨le_rfl, hl.1⟩
    simp [radialExtension, h0.1, h0.2, hl.2.2.2.2.1, hl.2.2.2.2.2.1,
      reductionK, Matrix.trace_smul, Matrix.trace_one]
    norm_num
  · exact radialSystem_reduced_away_zero hs hpos hx

-- @node: IsQuadraticFunction.restrict_line
/-- If [u is a quadratic function](hyp:hu), [its restriction to any line
through the origin, parametrized by t times a vector v, has the form at² + bt + c
for some real coefficients a, b, and c](goal). -/
lemma IsQuadraticFunction.restrict_line {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : IsQuadraticFunction u) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ a b c : ℝ, ∀ t : ℝ, u (t • v) = a * t ^ 2 + b * t + c := by
  obtain ⟨A, b, c, h⟩ := hu
  refine ⟨⟪v, WithLp.toLp 2 (A *ᵥ v)⟫, ⟪b, v⟫, c, ?_⟩
  intro t
  have hA : WithLp.toLp 2 (A *ᵥ (t • v : EuclideanSpace ℝ (Fin n))) =
      t • (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℝ (Fin n)) := by
    ext i
    change (A *ᵥ (t • (fun i => v i))) i = t * (A *ᵥ (fun i => v i)) i
    rw [Matrix.mulVec_smul]
    rfl
  rw [h, hA, inner_smul_left, inner_smul_right, inner_smul_right]
  simp only [conj_trivial]
  ring

-- @node: reductionGraph_time_axis
/-- If [F equals one at the origin](hyp:hF), [the square-root reduction graph
at time t on the time axis equals the square root of 1 + t²](goal). -/
lemma reductionGraph_time_axis {m : ℕ} {F : EuclideanSpace ℝ (Fin m) → ℝ}
    (hF : F 0 = 1) (t : ℝ) :
    reductionGraph F (t • timeBasis m) = Real.sqrt (1 + t ^ 2) := by
  have hx : xPart (t • timeBasis m) = 0 := by
    ext i
    simp [xPart, timeBasis]
  have ht : tPart (t • timeBasis m) = t := by
    simp [tPart, timeBasis]
  simp [reductionGraph, hx, ht, hF]

-- @node: reductionGraph_not_quadratic
/-- If [F equals one at the origin](hyp:hF), [its square-root reduction graph
is not a quadratic function](goal). -/
lemma reductionGraph_not_quadratic {m : ℕ} {F : EuclideanSpace ℝ (Fin m) → ℝ}
    (hF : F 0 = 1) : ¬ IsQuadraticFunction (reductionGraph F) := by
  intro hquad
  obtain ⟨a, b, c, h⟩ := hquad.restrict_line (timeBasis m)
  simp only [reductionGraph_time_axis hF] at h
  have hc : c = 1 := by simpa using (h 0).symm
  subst c
  have h1 := h 1
  have hn1 := h (-1)
  norm_num at h1 hn1
  have hb : b = 0 := by linarith
  subst b
  have h2 := h 2
  norm_num at h2
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  rw [h1] at hs2
  rw [h2] at hs5
  nlinarith [sq_nonneg a]

-- @node: thm:main
/-- [There exists an infinitely differentiable real-valued function on all of
ten-dimensional Euclidean space that is not quadratic, has a positive definite
Hessian everywhere, and satisfies the affine maximal equation: the sum of the
entrywise products of its Hessian adjugate and the Hessian of its Hessian
determinant raised to −11/12 is zero at every point](goal). -/
theorem exists_nonquadratic_entire_affine_maximal :
    ∃ u : EuclideanSpace ℝ (Fin 10) → ℝ, -- @realizes u(entire graph in dimension ten)
      ContDiff ℝ ∞ u ∧ -- @realizes u(smoothness on all of Euclidean space)
      ¬ IsQuadraticFunction u ∧
      HessianPositive u Set.univ ∧
      ∀ z, ∑ i : Fin 10, ∑ j : Fin 10,
        (hessianMatrix u z).adjugate i j *
          hessianMatrix (fun z' => (hessianMatrix u z').det ^ (-(11 / 12 : ℝ))) z i j =
            0 := by
  obtain ⟨ε, hε, F₀, P₀, hl⟩ := exists_local_radial_solution
  obtain ⟨F, P, heq, hs, hpos, hFs, hPs, hH⟩ :=
    local_radial_solution_extends_globally ε F₀ P₀ hl
  have h0 := heq 0 ⟨le_rfl, hε⟩
  have hF0 : radialExtension 9 F 0 = 1 := by
    simpa [radialExtension, h0.1] using hl.2.2.2.2.1
  have hP0 : radialExtension 9 P 0 = 1 := by
    simpa [radialExtension, h0.2] using hl.2.2.2.2.2.1
  have hFP : ReductionFunctions univ (radialExtension 9 F) (radialExtension 9 P) := by
    refine ⟨isOpen_univ, hFs.contDiffOn, hPs.contDiffOn, ?_⟩
    intro x _
    by_cases hx : x = 0
    · subst x
      rw [hF0, hP0]
      exact ⟨zero_lt_one, zero_lt_one⟩
    · exact ⟨(hpos ‖x‖ (norm_pos_iff.mpr hx)).1,
        (hpos ‖x‖ (norm_pos_iff.mpr hx)).2.1⟩
  have hH' : ReductionHessianPosDef univ (radialExtension 9 F) := fun x _ => hH x
  have hsys := radialSystem_reduced_everywhere hl heq hs hpos
  have hred := reduction_affineMaximal
    (by norm_num [ReductionDimension] : ReductionDimension 9) hFP hH' hsys
  refine ⟨reductionGraph (radialExtension 9 F), ?_, reductionGraph_not_quadratic hF0, ?_, ?_⟩
  · exact contDiff_iff_contDiffAt.mpr fun z => reductionGraph_contDiffAt hFP (mem_univ _)
  · exact fun z _ => hred.1 z (mem_univ _)
  · intro z
    have he := hred.2 z (mem_univ _)
    unfold cofactorMatrix affineWeight at he
    norm_num at he
    exact he

end OaiSmoothNonquadraticAffine
