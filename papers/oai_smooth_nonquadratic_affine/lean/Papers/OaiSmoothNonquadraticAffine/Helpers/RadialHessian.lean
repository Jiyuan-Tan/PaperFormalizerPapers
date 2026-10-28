module

public import Papers.OaiSmoothNonquadraticAffine.TReduction
public import Papers.OaiSmoothNonquadraticAffine.Helpers.RadialSmooth
public import Mathlib.Algebra.Order.Star.Real

/-! # Positive Hessians of the continued radial profiles

The radial and tangential coefficients are the second radial derivative and
its first derivative divided by the radius. At the origin, agreement with the
local profiles preserves the identity Hessian.
-/

public section

open Set Filter
open scoped Topology ContDiff

namespace OaiSmoothNonquadraticAffine

-- @node: radialExtension_hessian_zero_of_local
/-- If [F₀ and P₀ form a local solution on a neighborhood of radius
ε](hyp:hLocal) and [F agrees with F₀ at every radius from zero inclusive to
ε exclusive](hyp:heq), then [the Hessian at the origin of the nine-dimensional
radial extension of F is the identity matrix](goal). -/
lemma radialExtension_hessian_zero_of_local {ε : ℝ} {F₀ P₀ F : ℝ → ℝ}
    (hLocal : LocalSolutionData ε F₀ P₀)
    (heq : ∀ r ∈ Ico 0 ε, F r = F₀ r) :
    hessianMatrix (radialExtension 9 F) 0 = 1 := by
  have hg : radialExtension 9 F =ᶠ[𝓝 0] radialExtension 9 F₀ := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 9)) hLocal.1] with x hx
    exact heq ‖x‖ ⟨norm_nonneg x, by simpa using hx⟩
  rw [hessianMatrix_congr hg]
  exact hLocal.2.2.2.2.2.2.1

-- @node: radialNorm_hasFDerivAt
/-- At [a nonzero vector x](hyp:hx), [the Euclidean norm has derivative given
by the linear map sending an increment to its inner product with x divided
by the norm of x](goal). -/
lemma radialNorm_hasFDerivAt {m : ℕ} {x : EuclideanSpace ℝ (Fin m)} (hx : x ≠ 0) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin m) => ‖z‖)
      (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hd := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hx)))
  simpa [Real.sqrt_sq (norm_nonneg _), two_smul, smul_add, ← add_smul,
    mul_inv_rev, ← mul_two] using hd

-- @node: radialExtension_fderiv
/-- At [a nonzero vector x](hyp:hx), if [F is differentiable at the norm of
x](hyp:hF), then [the derivative of its radial extension is the linear map
sending an increment v to F′ at the norm of x times the inner product of x
and v divided by the norm of x](goal). -/
lemma radialExtension_fderiv {m : ℕ} {F : ℝ → ℝ}
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ≠ 0)
    (hF : DifferentiableAt ℝ F ‖x‖) :
    fderiv ℝ (radialExtension m F) x =
      (deriv F ‖x‖ / ‖x‖) • innerSL ℝ x := by
  change fderiv ℝ (fun z : EuclideanSpace ℝ (Fin m) => F ‖z‖) x = _
  have hd := hF.hasDerivAt.comp_hasFDerivAt x (radialNorm_hasFDerivAt hx)
  simpa only [radialExtension, Function.comp_def, smul_smul, div_eq_mul_inv] using hd.fderiv

-- @node: radialExtension_secondDifferential
/-- If [F is twice continuously differentiable at positive radii](hyp:hF),
then at [any nonzero vector x](hyp:hx), [the second differential of its radial
extension in any direction v equals F″ at the norm of x times the squared
length of v's radial component, plus F′ at the norm of x divided by that norm
times the squared length of v's tangential component](goal).

The squared radial component is the squared inner product of x and v divided
by the squared norm of x; the squared tangential component is the squared
norm of v minus that quantity. -/
lemma radialExtension_secondDifferential {m : ℕ} {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ 2 F (Ioi 0)) {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ≠ 0) (v : EuclideanSpace ℝ (Fin m)) :
    secondDifferential (radialExtension m F) x v v =
      deriv (deriv F) ‖x‖ * (inner ℝ x v ^ 2 / ‖x‖ ^ 2) +
      deriv F ‖x‖ / ‖x‖ * (‖v‖ ^ 2 - inner ℝ x v ^ 2 / ‖x‖ ^ 2) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hs := hF.contDiffAt (isOpen_Ioi.mem_nhds hr)
  have hsp : ContDiffAt ℝ 2 (radialExtension m F) x :=
    radialExtension_contDiffAt_of_pos hF hx
  have hdf : DifferentiableAt ℝ (deriv F) ‖x‖ :=
    (hs.derivWithin (m := 1) (by norm_num)).differentiableAt_one
  have hq := hdf.hasDerivAt.div (hasDerivAt_id ‖x‖) hr.ne'
  have hqc := hq.comp_hasFDerivAt x (radialNorm_hasFDerivAt hx)
  have heq : (fun z => fderiv ℝ (radialExtension m F) z v) =ᶠ[𝓝 x]
      (fun z => (deriv F ‖z‖ / ‖z‖) * innerSL ℝ v z) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with z hz
    rw [radialExtension_fderiv hz
      ((hF.contDiffAt (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr hz))).differentiableAt
        (by norm_num))]
    simp [real_inner_comm]
  have hprod := hqc.mul (innerSL ℝ v).hasFDerivAt
  simp only [Function.comp_def, Pi.div_apply, id_eq] at hprod
  change HasFDerivAt (fun z => (deriv F ‖z‖ / ‖z‖) * innerSL ℝ v z) _ x at hprod
  rw [secondDifferential_eq hsp, heq.fderiv_eq, hprod.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    smul_eq_mul, innerSL_apply_apply, real_inner_comm v x, real_inner_self_eq_norm_sq,
    mul_one]
  field_simp
  ring

-- @node: radialExtension_hessian_posDef_of_pos
/-- If [F is twice continuously differentiable at positive radii](hyp:hF),
[x is nonzero](hyp:hx), [F′ is strictly positive at the norm of x](hyp:hy),
and [F″ is strictly positive there](hyp:hyy), then [the Hessian of the radial
extension of F at x is positive definite](goal). -/
lemma radialExtension_hessian_posDef_of_pos {m : ℕ} {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ 2 F (Ioi 0)) {x : EuclideanSpace ℝ (Fin m)}
    (hx : x ≠ 0) (hy : 0 < deriv F ‖x‖) (hyy : 0 < deriv (deriv F) ‖x‖) :
    (hessianMatrix (radialExtension m F) x).PosDef := by
  have hs := radialExtension_contDiffAt_of_pos hF hx
  have hr := norm_pos_iff.mpr hx
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hessianMatrix_isHermitian hs) ?_
  intro a ha
  let v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 a
  have hv : v ≠ 0 := by
    intro h
    exact ha (congrArg WithLp.ofLp h)
  suffices 0 < secondDifferential (radialExtension m F) x v v by
    simpa only [secondDifferential_eq_dotProduct hs, star_trivial] using this
  rw [radialExtension_secondDifferential hF hx]
  have ha0 : 0 ≤ inner ℝ x v ^ 2 / ‖x‖ ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hcs : inner ℝ x v ^ 2 ≤ ‖v‖ ^ 2 * ‖x‖ ^ 2 := by
    simpa only [← sq, real_inner_self_eq_norm_sq, mul_comm] using
      real_inner_mul_inner_self_le x v
  have hb0 : 0 ≤ ‖v‖ ^ 2 - inner ℝ x v ^ 2 / ‖x‖ ^ 2 :=
    sub_nonneg.mpr ((div_le_iff₀ (sq_pos_of_pos hr)).mpr hcs)
  have hc : 0 < deriv F ‖x‖ / ‖x‖ := div_pos hy hr
  by_cases hz : inner ℝ x v ^ 2 / ‖x‖ ^ 2 = 0
  · rw [hz, mul_zero, zero_add, sub_zero]
    exact mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hv))
  · exact add_pos_of_pos_of_nonneg (mul_pos hyy (lt_of_le_of_ne ha0 (Ne.symm hz)))
      (mul_nonneg hc.le hb0)

-- @node: radialSystem_hessian_posDef_of_local
/-- If [F₀ and P₀ form a local solution of radius ε](hyp:hLocal), [F and P
agree with them at radii from zero inclusive to ε exclusive](hyp:heq),
[F and P solve the radial system at every positive radius](hyp:hsys),
[P is strictly positive at positive radii](hyp:hP), [F′ is strictly positive
there](hyp:hy), and [F″ is strictly positive there](hyp:hyy), then [the Hessian
of the nine-dimensional radial extension of F is positive definite at every
point](goal). -/
lemma radialSystem_hessian_posDef_of_local {ε : ℝ} {F₀ P₀ F P : ℝ → ℝ}
    (hLocal : LocalSolutionData ε F₀ P₀)
    (heq : ∀ r ∈ Ico 0 ε, F r = F₀ r ∧ P r = P₀ r)
    (hsys : RadialSystem radialDim radialK radialGamma F P (Ioi 0))
    (hP : ∀ r > 0, 0 < P r) (hy : ∀ r > 0, 0 < deriv F r)
    (hyy : ∀ r > 0, 0 < deriv (deriv F) r) :
    ∀ x, (hessianMatrix (radialExtension 9 F) x).PosDef := by
  have hs := (radialSystem_contDiffOn isOpen_Ioi hsys hP hy).1.of_le
    (show (2 : ℕ∞ω) ≤ ∞ by decide)
  intro x
  by_cases hx : x = 0
  · subst x
    rw [radialExtension_hessian_zero_of_local hLocal (fun r hr => (heq r hr).1)]
    exact Matrix.PosDef.one
  · exact radialExtension_hessian_posDef_of_pos hs hx
      (hy ‖x‖ (norm_pos_iff.mpr hx)) (hyy ‖x‖ (norm_pos_iff.mpr hx))

end OaiSmoothNonquadraticAffine
