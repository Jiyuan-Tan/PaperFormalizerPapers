module

public import Papers.OaiSmoothNonquadraticAffine.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Adapted vectors and scalar identities for the square-root reduction -/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace OaiSmoothNonquadraticAffine

/-- For [a spatial function F](hyp:F) and [a point z with spatial coordinates x
and last coordinate t](hyp:z), assuming [F is positive at x](hyp:_hF), the
[normalized last coordinate](goal) is t divided by F at x. -/
def reductionZeta {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (z : EuclideanSpace ℝ (Fin (m + 1))) (_hF : 0 < F (xPart z)) : ℝ :=
  tPart z / F (xPart z) -- @realizes \zeta(normalized last coordinate t/F)

/-- For [spatial dimension m](hyp:m) and [a real argument ζ](hyp:ζ), the
[scalar reduction factor h](goal) is (1 + ζ²) raised to (m + 2)/2. -/
def reductionH (m : ℕ) (ζ : ℝ) : ℝ :=
  (1 + ζ ^ 2) ^ (reductionK m / 2) -- @realizes h(positive scalar function of zeta)

/-- For [a spatial function F](hyp:F), [a point z with spatial coordinates x and
last coordinate t](hyp:z), [positivity of F at x](hyp:hF), and [a spatial coordinate
index i](hyp:i), the [adapted spatial vector](goal) is the i-th spatial unit vector
plus the last-coordinate unit vector multiplied by t/F at x times the i-th partial
derivative of F at x. -/
def adaptedSpatialBasis {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (z : EuclideanSpace ℝ (Fin (m + 1))) (hF : 0 < F (xPart z))
    (i : Fin m) : EuclideanSpace ℝ (Fin (m + 1)) := -- @realizes i(spatial index Fin m)
  spatialBasis m i +
    (reductionZeta F z hF * fderiv ℝ F (xPart z) (EuclideanSpace.single i 1)) •
      timeBasis m -- @realizes X_i(adapted spatial vector e_i+zeta F_i e_t)

-- @node: reductionH_hasDerivAt
/-- For any spatial dimension m and real argument ζ, [the scalar factor h has
derivative (m + 2)ζ times (1 + ζ²) raised to (m + 2)/2 − 1 at ζ](goal). -/
lemma reductionH_hasDerivAt (m : ℕ) (ζ : ℝ) :
    HasDerivAt (reductionH m)
      (reductionK m * ζ * (1 + ζ ^ 2) ^ (reductionK m / 2 - 1)) ζ := by
  have hpos : 0 < 1 + ζ ^ 2 := by positivity
  have hd : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * ζ) ζ := by
    simpa using ((hasDerivAt_id ζ).pow 2).const_add 1
  unfold reductionH
  convert! hd.rpow_const (p := reductionK m / 2) (Or.inl (ne_of_gt hpos)) using 1
  ring

-- @node: reductionH_deriv
/-- For any spatial dimension m and real argument ζ, [the derivative of the scalar
factor h at ζ equals (m + 2)ζ times (1 + ζ²) raised to (m + 2)/2 − 1](goal). -/
lemma reductionH_deriv (m : ℕ) (ζ : ℝ) :
    deriv (reductionH m) ζ =
      reductionK m * ζ * (1 + ζ ^ 2) ^ (reductionK m / 2 - 1) :=
  (reductionH_hasDerivAt m ζ).deriv

-- @node: reductionH_deriv_hasDerivAt
/-- For any spatial dimension m and real argument ζ, [the first derivative of h
has derivative (m + 2) times (1 + ζ²) raised to (m + 2)/2 − 1, plus
(m + 2)mζ² times (1 + ζ²) raised to (m + 2)/2 − 2, at ζ](goal). -/
lemma reductionH_deriv_hasDerivAt (m : ℕ) (ζ : ℝ) :
    HasDerivAt (deriv (reductionH m))
      (reductionK m * (1 + ζ ^ 2) ^ (reductionK m / 2 - 1) +
        reductionK m * (reductionK m - 2) * ζ ^ 2 *
          (1 + ζ ^ 2) ^ (reductionK m / 2 - 2)) ζ := by
  have hpos : 0 < 1 + ζ ^ 2 := by positivity
  have hd : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * ζ) ζ := by
    simpa using ((hasDerivAt_id ζ).pow 2).const_add 1
  have hp := hd.rpow_const (p := reductionK m / 2 - 1) (Or.inl (ne_of_gt hpos))
  have hh := ((hasDerivAt_id ζ).const_mul (reductionK m)).mul hp
  rw [show deriv (reductionH m) =
    (fun s => reductionK m * s * (1 + s ^ 2) ^ (reductionK m / 2 - 1)) from
      funext (reductionH_deriv m)]
  convert! hh using 1
  simp only [id_eq]
  ring_nf

-- @node: reductionH_second_deriv
/-- For any spatial dimension m and real argument ζ, [the second derivative of h
at ζ equals (m + 2) times (1 + ζ²) raised to (m + 2)/2 − 1, plus
(m + 2)mζ² times (1 + ζ²) raised to (m + 2)/2 − 2](goal). -/
lemma reductionH_second_deriv (m : ℕ) (ζ : ℝ) :
    deriv (deriv (reductionH m)) ζ =
      reductionK m * (1 + ζ ^ 2) ^ (reductionK m / 2 - 1) +
        reductionK m * (reductionK m - 2) * ζ ^ 2 *
          (1 + ζ ^ 2) ^ (reductionK m / 2 - 2) :=
  (reductionH_deriv_hasDerivAt m ζ).deriv

-- @node: reductionH_ode
/-- For any spatial dimension m and real argument ζ, [the scalar factor h satisfies
the differential equation (1 + ζ²)h″ − mζh′ = (m + 2)h at ζ](goal). -/
lemma reductionH_ode (m : ℕ) (ζ : ℝ) :
    (1 + ζ ^ 2) * deriv (deriv (reductionH m)) ζ -
      (m : ℝ) * ζ * deriv (reductionH m) ζ = reductionK m * reductionH m ζ := by
  have hne : 1 + ζ ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + ζ ^ 2)
  have hshift : (1 + ζ ^ 2) ^ (reductionK m / 2 - 1) =
      (1 + ζ ^ 2) ^ (reductionK m / 2 - 2) * (1 + ζ ^ 2) := by
    convert Real.rpow_add_one hne (reductionK m / 2 - 2) using 1
    congr 1
    ring
  have hshift' : (1 + ζ ^ 2) ^ (reductionK m / 2) =
      (1 + ζ ^ 2) ^ (reductionK m / 2 - 1) * (1 + ζ ^ 2) := by
    convert Real.rpow_add_one hne (reductionK m / 2 - 1) using 1
    congr 1
    ring
  rw [reductionH_second_deriv, reductionH_deriv, reductionH, hshift', hshift]
  unfold reductionK
  ring

-- @node: reduction_trace_vanishes
/-- If [F and P satisfy the reduced system on Ω](hyp:hSystem) and [x belongs to
Ω](hyp:hx), then, for any real ζ, [h at ζ times the trace of the inverse Hessian
of F times the Hessian of P at x, plus P at x divided by F at x times
((1 + ζ²)h″ − mζh′) at ζ, equals zero](goal). -/
lemma reduction_trace_vanishes {m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin m))}
    {F P : EuclideanSpace ℝ (Fin m) → ℝ} (hSystem : ReducedSystem m Ω F P)
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ Ω) (ζ : ℝ) :
    reductionH m ζ * Matrix.trace ((hessianMatrix F x)⁻¹ * hessianMatrix P x) +
      P x / F x * ((1 + ζ ^ 2) * deriv (deriv (reductionH m)) ζ -
        (m : ℝ) * ζ * deriv (reductionH m) ζ) = 0 := by
  rw [reductionH_ode]
  calc
    _ = reductionH m ζ *
        (Matrix.trace ((hessianMatrix F x)⁻¹ * hessianMatrix P x) +
          reductionK m * P x / F x) := by ring
    _ = 0 := by rw [(hSystem x hx).2, mul_zero]

-- @node: reductionH_pos
/-- For any spatial dimension m and real argument ζ, [the scalar reduction factor
h at ζ is strictly positive](goal). -/
lemma reductionH_pos (m : ℕ) (ζ : ℝ) : 0 < reductionH m ζ := by
  exact Real.rpow_pos_of_pos (by positivity) _

-- @node: reductionH_contDiff
/-- For any spatial dimension m, [the scalar reduction factor h is infinitely
differentiable on the real line](goal). -/
@[fun_prop] lemma reductionH_contDiff (m : ℕ) : ContDiff ℝ ∞ (reductionH m) := by
  unfold reductionH
  have hne : ∀ ζ : ℝ, 1 + ζ ^ 2 ≠ 0 := fun ζ => ne_of_gt (by positivity)
  fun_prop

-- @node: reducedSystem_P_from_det
/-- If [Ω is open and F and P are infinitely differentiable and strictly positive
on Ω](hyp:hFP), [F and P satisfy the reduced system on Ω](hyp:hSystem), and
[x belongs to Ω](hyp:hx), then [P at x equals the ratio of F at x to its Hessian
determinant at x, raised to (m + 2)/(m + 3)](goal). -/
lemma reducedSystem_P_from_det {m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin m))}
    {F P : EuclideanSpace ℝ (Fin m) → ℝ} (hFP : ReductionFunctions Ω F P)
    (hSystem : ReducedSystem m Ω F P) {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ Ω) :
    P x = (F x / (hessianMatrix F x).det) ^
      (((m : ℝ) + 2) / ((m : ℝ) + 3)) := by
  obtain ⟨hF, hP⟩ := hFP.2.2.2 x hx
  rw [(hSystem x hx).1]
  have hcancel : F x / (F x * P x ^ (-reductionGamma m)) =
      P x ^ (reductionGamma m) := by
    rw [Real.rpow_neg hP.le]
    field_simp
  rw [hcancel, ← Real.rpow_mul hP.le]
  have hexp : reductionGamma m * (((m : ℝ) + 2) / ((m : ℝ) + 3)) = 1 := by
    unfold reductionGamma
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    field_simp
  rw [hexp, Real.rpow_one]

-- @node: reduction_weight_from_ratio_det
/-- If [P is strictly positive](hyp:hP) and [d equals P raised to −(m + 3)/(m + 2)
times (1 + ζ²) raised to −(m + 3)/2](hyp:hd), then [d raised to
−(m + 2)/(m + 3) equals P times the scalar reduction factor h at ζ](goal). -/
lemma reduction_weight_from_ratio_det (m : ℕ) {P d ζ : ℝ} (hP : 0 < P)
    (hd : d = P ^ (-reductionGamma m) *
      (1 + ζ ^ 2) ^ (-((m : ℝ) + 3) / 2)) :
    d ^ (-((m : ℝ) + 2) / ((m : ℝ) + 3)) = P * reductionH m ζ := by
  have hz : 0 < 1 + ζ ^ 2 := by positivity
  rw [hd, Real.mul_rpow (Real.rpow_nonneg hP.le _) (Real.rpow_nonneg hz.le _),
    ← Real.rpow_mul hP.le, ← Real.rpow_mul hz.le]
  have hden : (m : ℝ) + 3 ≠ 0 := ne_of_gt (by positivity)
  have hden' : (m : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
  have hp : -reductionGamma m * (-((m : ℝ) + 2) / ((m : ℝ) + 3)) = 1 := by
    unfold reductionGamma
    field_simp
  have hzexp : (-((m : ℝ) + 3) / 2) *
      (-((m : ℝ) + 2) / ((m : ℝ) + 3)) = reductionK m / 2 := by
    unfold reductionK
    field_simp
  rw [hp, hzexp, Real.rpow_one]
  rfl

-- @node: reductionGraph_factorization
/-- If [F is strictly positive at the spatial coordinates x of z](hyp:hF), then
[the reduction graph at z equals F at x times the square root of
1 + (t/F at x)², where t is the last coordinate of z](goal). -/
lemma reductionGraph_factorization {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → ℝ) (z : EuclideanSpace ℝ (Fin (m + 1)))
    (hF : 0 < F (xPart z)) :
    reductionGraph F z =
      F (xPart z) * (1 + (tPart z / F (xPart z)) ^ 2) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  have hsq : F (xPart z) ^ 2 + tPart z ^ 2 =
      F (xPart z) ^ 2 * (1 + (tPart z / F (xPart z)) ^ 2) := by
    field_simp
  unfold reductionGraph
  rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hF.le]

-- @node: reduction_weight_from_det
/-- If [Ω is open and F and P are infinitely differentiable and strictly positive
on Ω](hyp:hFP), [F and P satisfy the reduced system on Ω](hyp:hSystem),
[the spatial coordinates x of z belong to Ω](hyp:hz), and [the Hessian determinant
of the reduction graph at z equals F at x raised to m + 2 times the graph value
raised to −(m + 3) times the Hessian determinant of F at x](hyp:hdet), then
[the affine weight of the reduction graph at z equals P at x times h evaluated
at t divided by F at x, where t is the last coordinate of z](goal). -/
lemma reduction_weight_from_det {m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin m))}
    {F P : EuclideanSpace ℝ (Fin m) → ℝ} (hFP : ReductionFunctions Ω F P)
    (hSystem : ReducedSystem m Ω F P)
    (z : EuclideanSpace ℝ (Fin (m + 1))) (hz : xPart z ∈ Ω)
    (hdet : (hessianMatrix (reductionGraph F) z).det =
      F (xPart z) ^ (m + 2) *
        (reductionGraph F z) ^ (-((m : ℝ) + 3)) * (hessianMatrix F (xPart z)).det) :
    affineWeight (m + 1) (reductionGraph F) z =
      P (xPart z) * reductionH m (tPart z / F (xPart z)) := by
  obtain ⟨hF, hP⟩ := hFP.2.2.2 (xPart z) hz
  have hzpos : 0 < 1 + (tPart z / F (xPart z)) ^ 2 := by positivity
  have hnormalized : (hessianMatrix (reductionGraph F) z).det =
      P (xPart z) ^ (-reductionGamma m) *
        (1 + (tPart z / F (xPart z)) ^ 2) ^ (-((m : ℝ) + 3) / 2) := by
    rw [hdet, (hSystem (xPart z) hz).1, reductionGraph_factorization F z hF,
      Real.mul_rpow hF.le (Real.rpow_nonneg hzpos.le _), ← Real.rpow_mul hzpos.le]
    rw [show (1 / 2 : ℝ) * (-((m : ℝ) + 3)) = -((m : ℝ) + 3) / 2 by ring]
    have hcancel : F (xPart z) ^ (m + 2) *
        F (xPart z) ^ (-((m : ℝ) + 3)) * F (xPart z) = 1 := by
      rw [← Real.rpow_natCast]
      conv_lhs => arg 2; rw [← Real.rpow_one (F (xPart z))]
      rw [← Real.rpow_add hF, ← Real.rpow_add hF]
      convert Real.rpow_zero (F (xPart z)) using 1
      congr 1
      push_cast
      ring
    calc
      _ = (F (xPart z) ^ (m + 2) *
          F (xPart z) ^ (-((m : ℝ) + 3)) * F (xPart z)) *
          (P (xPart z) ^ (-reductionGamma m) *
            (1 + (tPart z / F (xPart z)) ^ 2) ^ (-((m : ℝ) + 3) / 2)) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have hw := reduction_weight_from_ratio_det m hP hnormalized
  unfold affineWeight
  convert hw using 2
  push_cast
  ring

end OaiSmoothNonquadraticAffine
