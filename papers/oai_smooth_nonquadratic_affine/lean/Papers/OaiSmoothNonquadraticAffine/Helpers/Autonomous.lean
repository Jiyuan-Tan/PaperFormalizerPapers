module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.Local
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Logarithmic coordinates of the maximal positive continuation -/

public section

open Filter Set
open scoped Topology ContDiff

namespace OaiSmoothNonquadraticAffine

-- @node: radial_second_derivative_pos
/-- If [F and P form a positive radial solution up to R](hyp:hSol) and [r lies
in its positive continuation interval](hyp:hr), then [the second derivative of F
at r is strictly positive](goal). -/
lemma radial_second_derivative_pos {F P : ℝ → ℝ} {R : WithTop ℝ}
    (hSol : PositiveRadialSolution F P R) {r : ℝ} (hr : r ∈ radialInterval R) :
    0 < deriv (deriv F) r := by
  have heq := (hSol.2.1 r hr).2.2.1
  have hp := hSol.2.2 r hr
  have hright : 0 < r ^ (radialDim - 1) * F r * P r ^ (-radialGamma) :=
    mul_pos (mul_pos (pow_pos hr.1 _) hp.1) (Real.rpow_pos_of_pos hp.2.1 _)
  exact (mul_pos_iff_of_pos_left (pow_pos hp.2.2 _)).mp (heq ▸ hright)

-- @node: radial_coordinate_domain_of_positive
/-- If [F and P form a positive radial solution up to R](hyp:hSol) and [r lies
in its positive continuation interval](hyp:hr), then [r is positive, F, P and
the first derivative of F are nonzero there, and the ratio r times the second
derivative of F divided by its first derivative is positive](goal). -/
lemma radial_coordinate_domain_of_positive {F P : ℝ → ℝ} {R : WithTop ℝ}
    (hSol : PositiveRadialSolution F P R) {r : ℝ} (hr : r ∈ radialInterval R) :
    RadialCoordinateDomain F P r := by
  have hp := hSol.2.2 r hr
  exact ⟨hr.1, ne_of_gt hp.1, ne_of_gt hp.2.1, ne_of_gt hp.2.2,
    div_pos (mul_pos hr.1 (radial_second_derivative_pos hSol hr)) hp.2.2⟩

-- @node: radialCoordinates_eq_of_domain
/-- If [r is positive, F, P and the first derivative of F are nonzero at r, and
B is positive there](hyp:h), then [the radial coordinate vector equals (A, B, C/B),
where A is r times the first derivative of F divided by F, B is r times the
second derivative of F divided by its first derivative, and C is minus r times
the derivative of P divided by P, all evaluated at r](goal). -/
lemma radialCoordinates_eq_of_domain {F P : ℝ → ℝ} {r : ℝ}
    (h : RadialCoordinateDomain F P r) :
    radialCoordinates F P r =
      ![r * deriv F r / F r, r * deriv (deriv F) r / deriv F r,
        (-(r * deriv P r / P r)) / (r * deriv (deriv F) r / deriv F r)] := by
  simp [radialCoordinates, h, ratioA, ratioB, ratioC, ratioD]

-- @node: radial_coordinates_first_two_pos
/-- If [F and P form a positive radial solution up to R](hyp:hSol) and [r lies
in its positive continuation interval](hyp:hr), then [the first two radial
coordinates at r are strictly positive](goal). -/
lemma radial_coordinates_first_two_pos {F P : ℝ → ℝ} {R : WithTop ℝ}
    (hSol : PositiveRadialSolution F P R) {r : ℝ} (hr : r ∈ radialInterval R) :
    0 < radialCoordinates F P r 0 ∧ 0 < radialCoordinates F P r 1 := by
  have hd := radial_coordinate_domain_of_positive hSol hr
  rw [radialCoordinates_eq_of_domain hd]
  exact ⟨div_pos (mul_pos hr.1 (hSol.2.2 r hr).2.2) (hSol.2.2 r hr).1, hd.2.2.2.2⟩

-- @node: radialInterval_mem_nhds
/-- If [r lies in the positive radial interval ending at R](hyp:hr), then
[that interval contains a neighborhood of r](goal). -/
lemma radialInterval_mem_nhds {R : WithTop ℝ} {r : ℝ} (hr : r ∈ radialInterval R) :
    radialInterval R ∈ 𝓝 r := by
  cases R with
  | top => simpa [radialInterval, Ioi] using Ioi_mem_nhds hr.1
  | coe a =>
    have h : r ∈ Ioo 0 a := by simpa [radialInterval] using hr
    simpa [radialInterval, Ioo] using isOpen_Ioo.mem_nhds h

-- @node: radial_ratioB_eq
/-- If [F and P form a positive radial solution up to R](hyp:hSol) and [r lies
in its positive continuation interval](hyp:hr), then [r times the second derivative
of F divided by its first derivative equals r to the ninth power times F times
P to the power −12/11, divided by the ninth power of the first derivative of F,
all evaluated at r](goal). -/
lemma radial_ratioB_eq {F P : ℝ → ℝ} {R : WithTop ℝ}
    (hSol : PositiveRadialSolution F P R) {r : ℝ} (hr : r ∈ radialInterval R) :
    r * deriv (deriv F) r / deriv F r =
      r ^ 9 * F r * P r ^ (-radialGamma) / deriv F r ^ 9 := by
  have heq := (hSol.2.1 r hr).2.2.1
  have hy := ne_of_gt (hSol.2.2 r hr).2.2
  dsimp [radialDim] at heq
  field_simp
  nlinarith [congrArg (fun a : ℝ => r * a) heq]

-- @node: radial_scalar_log_derivatives
/-- If [F and P form a positive radial solution up to R](hyp:hSol) and [r lies
in its positive continuation interval](hyp:hr), then [the radial derivatives of
A, B and C at r are respectively A(1 + B − A)/r,
B(9 + A + (12/11)C − 9B)/r, and (C(1 + C − 8B) + 11AB)/r, where
A = rF′/F, B = rF″/F′ and C = −rP′/P](goal). -/
lemma radial_scalar_log_derivatives {F P : ℝ → ℝ} {R : WithTop ℝ}
    (hSol : PositiveRadialSolution F P R) {r : ℝ} (hr : r ∈ radialInterval R) :
    let a := r * deriv F r / F r
    let b := r * deriv (deriv F) r / deriv F r
    let c := -(r * deriv P r / P r)
    HasDerivAt (fun s => s * deriv F s / F s) (a * (1 + b - a) / r) r ∧
    HasDerivAt (fun s => s * deriv (deriv F) s / deriv F s)
      (b * (9 + a + radialGamma * c - 9 * b) / r) r ∧
    HasDerivAt (fun s => -(s * deriv P s / P s))
      ((c * (1 + c - 8 * b) + 11 * a * b) / r) r := by
  dsimp only
  have hp := hSol.2.2 r hr
  have hnF := ne_of_gt hp.1
  have hnP := ne_of_gt hp.2.1
  have hny := ne_of_gt hp.2.2
  have hnr := ne_of_gt hr.1
  have hs := hSol.2.1 r hr
  have hF := (hs.1.differentiableAt (by norm_num)).hasDerivAt
  have hP := (hs.2.1.differentiableAt (by norm_num)).hasDerivAt
  have hy := ((hs.1.derivWithin (m := 1) (by norm_num)).differentiableAt_one).hasDerivAt
  have hz := ((hs.2.1.derivWithin (m := 1) (by norm_num)).differentiableAt_one).hasDerivAt
  have hi := hasDerivAt_id r
  have hA := (hi.mul hy).div hF hnF
  have hBraw := (((hi.pow 9).mul hF).mul
    (hP.rpow_const (p := -radialGamma) (Or.inl hnP))).div (hy.pow 9) (pow_ne_zero _ hny)
  rw [Real.rpow_sub_one hnP] at hBraw
  have hBraw' : HasDerivAt
      (fun s => s ^ 9 * F s * P s ^ (-radialGamma) / deriv F s ^ 9)
      ((r ^ 9 * F r * P r ^ (-radialGamma) / deriv F r ^ 9) *
        (9 / r + deriv F r / F r - radialGamma * deriv P r / P r -
          9 * deriv (deriv F) r / deriv F r)) r := by
    convert! hBraw using 1
    dsimp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq]
    field_simp [hnr, hnF, hnP, hny]
    ring
  have hB := hBraw'.congr_of_eventuallyEq
    (Filter.Eventually.mono (radialInterval_mem_nhds hr) fun s hs => radial_ratioB_eq hSol hs)
  rw [← radial_ratioB_eq hSol hr] at hB
  have hC := ((hi.mul hz).div hP hnP).neg
  have hflux := ((hy.pow 8).mul hz).deriv
  have heqY := hs.2.2.1
  have heqZ := hs.2.2.2
  dsimp [radialDim, radialK] at heqY heqZ
  change deriv (fun s => deriv F s ^ 8 * deriv P s) r = _ at hflux
  rw [hflux] at heqZ
  dsimp only [Pi.pow_apply] at heqZ
  norm_num only at heqZ
  have hpow : P r ^ (1 - radialGamma) = P r * P r ^ (-radialGamma) := by
    rw [sub_eq_add_neg, Real.rpow_add hp.2.1, Real.rpow_one]
  rw [hpow] at heqZ
  have hZ : 8 * F r * deriv (deriv F) r * deriv P r +
      F r * deriv F r * deriv (deriv P) r =
        -11 * P r * deriv F r * deriv (deriv F) r := by
    apply mul_left_cancel₀ (pow_ne_zero 7 hny)
    linear_combination F r * heqZ + 11 * P r * heqY
  refine ⟨?_, ?_, ?_⟩
  · convert! hA using 1
    dsimp only [Pi.mul_apply, Pi.div_apply, id_eq]
    field_simp [hnr, hnF, hnP, hny]
  · convert! hB using 1
    field_simp [hnr, hnF, hnP, hny]
    ring
  · convert! hC using 1
    dsimp only [Pi.mul_apply, Pi.div_apply, Pi.neg_apply, id_eq]
    field_simp [hnr, hnF, hnP, hny]
    linear_combination r * P r * hZ

-- @node: radial_coordinates_log_derivative
/-- If [F and P form a positive radial solution up to R](hyp:hSol) and [r lies
in its positive continuation interval](hyp:hr), then [the derivative of the radial
coordinate vector with respect to logarithmic radius at log r equals the
autonomous field evaluated at the radial coordinates at r](goal). -/
lemma radial_coordinates_log_derivative {F P : ℝ → ℝ} {R : WithTop ℝ}
    (hSol : PositiveRadialSolution F P R) {r : ℝ} (hr : r ∈ radialInterval R) :
    HasDerivAt (fun τ => radialCoordinates F P (Real.exp τ))
      (autonomousField (radialCoordinates F P r)) (Real.log r) := by
  let a : ℝ → ℝ := fun s => s * deriv F s / F s
  let b : ℝ → ℝ := fun s => s * deriv (deriv F) s / deriv F s
  let c : ℝ → ℝ := fun s => -(s * deriv P s / P s)
  obtain ⟨ha, hb, hc⟩ := radial_scalar_log_derivatives hSol hr
  have hd := radial_coordinate_domain_of_positive hSol hr
  have hnb : b r ≠ 0 := ne_of_gt hd.2.2.2.2
  have hnr : r ≠ 0 := ne_of_gt hr.1
  have hdc := hc.div hb hnb
  let v : Fin 3 → ℝ :=
    ![a r * (1 + b r - a r) / r,
      b r * (9 + a r + radialGamma * c r - 9 * b r) / r,
      (((c r * (1 + c r - 8 * b r) + 11 * a r * b r) / r) * b r -
        c r * (b r * (9 + a r + radialGamma * c r - 9 * b r) / r)) / b r ^ 2]
  have hv : HasDerivAt (fun s => ![a s, b s, c s / b s]) v r := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [a, b, c, v] using! ha
    · simpa [a, b, c, v] using! hb
    · simpa [a, b, c, v] using! hdc
  have hcoords : radialCoordinates F P =ᶠ[𝓝 r] (fun s => ![a s, b s, c s / b s]) :=
    Filter.Eventually.mono (radialInterval_mem_nhds hr) fun s hs =>
      radialCoordinates_eq_of_domain (radial_coordinate_domain_of_positive hSol hs)
  have hrad := hv.congr_of_eventuallyEq hcoords
  have hrad' : HasDerivAt (radialCoordinates F P) v (Real.exp (Real.log r)) := by
    simpa only [Real.exp_log hr.1] using hrad
  have hcomp := hrad'.scomp (Real.log r) (Real.hasDerivAt_exp (Real.log r))
  rw [Real.exp_log hr.1] at hcomp
  convert! hcomp using 1
  ext i
  rw [radialCoordinates_eq_of_domain hd]
  fin_cases i <;> simp only [autonomousField, v, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · change a r * (1 + b r - a r) = r * (a r * (1 + b r - a r) / r)
    field_simp
  · change b r * (9 + a r + (12 / 11 : ℝ) * b r * (c r / b r) - 9 * b r) =
      r * (b r * (9 + a r + radialGamma * c r - 9 * b r) / r)
    dsimp [radialGamma]
    field_simp
  · change (11 - c r / b r) * a r - 8 * (c r / b r) +
        b r * (c r / b r) * (1 - c r / b r / 11) = _
    dsimp [radialGamma]
    field_simp
    ring

-- @node: radial_profile_origin_jets
/-- If [ε is positive](hyp:hε) and [the nine-dimensional radial extension of f
is infinitely differentiable on the open ball of radius ε centered at zero](hyp:hf),
then [the even profile f of the absolute radius is twice continuously differentiable
at zero, its first derivative there vanishes, and its second derivative equals
the first diagonal entry of the radial extension's Hessian at the origin](goal). -/
lemma radial_profile_origin_jets {ε : ℝ} {f : ℝ → ℝ} (hε : 0 < ε)
    (hf : ContDiffOn ℝ ∞ (radialExtension 9 f) (Metric.ball 0 ε)) :
    ContDiffAt ℝ 2 (fun r => f |r|) 0 ∧
    deriv (fun r => f |r|) 0 = 0 ∧
    deriv (deriv (fun r => f |r|)) 0 =
      hessianMatrix (radialExtension 9 f) 0 0 0 := by
  let e : EuclideanSpace ℝ (Fin 9) := EuclideanSpace.single 0 1
  let G := radialExtension 9 f
  let L : ℝ → EuclideanSpace ℝ (Fin 9) := fun r => r • e
  have hL : ContDiff ℝ ∞ L := by fun_prop
  have hLd (r : ℝ) : HasDerivAt L e r := by
    simpa [L] using (hasDerivAt_id r).smul_const e
  have hG : ContDiffAt ℝ 2 G 0 :=
    (hf.contDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hε))).of_le (by decide)
  have hcomp : (fun r => G (L r)) = (fun r => f |r|) := by
    funext r
    simp [G, L, e, radialExtension, norm_smul, Real.norm_eq_abs]
  have hzero : L 0 = 0 := by simp [L]
  have hg : ContDiffAt ℝ 2 (fun r => f |r|) 0 := by
    rw [← hcomp]
    have hG' : ContDiffAt ℝ 2 G (L 0) := by simpa only [hzero] using hG
    have hL2 : ContDiffAt ℝ 2 L 0 := hL.contDiffAt.of_le (by decide)
    exact hG'.comp 0 hL2
  have hH : ContDiffAt ℝ 1 (fun x => fderiv ℝ G x e) 0 :=
    (hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hnear : ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℝ (Fin 9)), DifferentiableAt ℝ G x := by
    filter_upwards [hG.eventually (by norm_num)] with x hx
    exact hx.differentiableAt (by norm_num)
  have heq : deriv (fun r => f |r|) =ᶠ[𝓝 0] (fun r => fderiv ℝ G (L r) e) := by
    filter_upwards
      [(hL.continuous.continuousAt (x := 0)).tendsto.eventually (hzero ▸ hnear)] with r hr
    rw [← hcomp]
    exact (hr.hasFDerivAt.comp_hasDerivAt r (hLd r)).deriv
  have hsecond : deriv (deriv (fun r => f |r|)) 0 = hessianMatrix G 0 0 0 := by
    rw [heq.deriv_eq]
    have hH' : DifferentiableAt ℝ (fun x => fderiv ℝ G x e) (L 0) := by
      simpa only [hzero] using hH.differentiableAt_one
    simpa [hzero, hessianMatrix, e, Function.comp_def] using
      (hH'.hasFDerivAt.comp_hasDerivAt 0 (hLd 0)).deriv
  have hneg := hg.differentiableAt (by norm_num) |>.hasDerivAt
  have hneg' := hneg.comp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).neg) (by simp)
  have hsame : (fun r : ℝ => f |r|) ∘ (-id) = (fun r => f |r|) := by
    funext r
    simp
  rw [hsame] at hneg'
  have heven : deriv (fun r => f |r|) 0 = 0 := by
    have hh := hneg.unique hneg'
    linarith
  exact ⟨hg, heven, hsecond⟩

-- @node: radial_profile_origin_limits
/-- If [ε is positive](hyp:hε) and [the nine-dimensional radial extension of f
is infinitely differentiable on the open ball of radius ε centered at zero](hyp:hf),
then [as the radius decreases to zero, f tends to its value at zero, its first
derivative tends to zero, and both its second derivative and its first derivative
divided by the radius tend to the first diagonal entry of the radial extension's
Hessian at the origin](goal). -/
lemma radial_profile_origin_limits {ε : ℝ} {f : ℝ → ℝ} (hε : 0 < ε)
    (hf : ContDiffOn ℝ ∞ (radialExtension 9 f) (Metric.ball 0 ε)) :
    Tendsto f (𝓝[>] 0) (𝓝 (f 0)) ∧
    Tendsto (deriv f) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (deriv (deriv f)) (𝓝[>] 0)
      (𝓝 (hessianMatrix (radialExtension 9 f) 0 0 0)) ∧
    Tendsto (fun r => deriv f r / r) (𝓝[>] 0)
      (𝓝 (hessianMatrix (radialExtension 9 f) 0 0 0)) := by
  obtain ⟨hg, heven, hsecond⟩ := radial_profile_origin_jets hε hf
  let g : ℝ → ℝ := fun r => f |r|
  change deriv g 0 = 0 at heven
  change deriv (deriv g) 0 = _ at hsecond
  have heq (r : ℝ) (hr : 0 < r) : f =ᶠ[𝓝 r] g := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    simp [g, abs_of_pos (show 0 < s from hs)]
  have hge : f =ᶠ[𝓝[>] 0] g := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (heq r hr).eq_of_nhds
  have hde : deriv f =ᶠ[𝓝[>] 0] deriv g := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (heq r hr).deriv_eq
  have hdde : deriv (deriv f) =ᶠ[𝓝[>] 0] deriv (deriv g) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (heq r hr).deriv.deriv_eq
  have hg1 : ContDiffAt ℝ 1 (deriv g) 0 := hg.derivWithin (by norm_num)
  have hg2 : ContDiffAt ℝ 0 (deriv (deriv g)) 0 := hg1.derivWithin (by norm_num)
  have hzero : Tendsto g (𝓝[>] 0) (𝓝 (f 0)) := by
    simpa [g] using hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hone : Tendsto (deriv g) (𝓝[>] 0) (𝓝 0) := by
    simpa only [heven] using hg1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have htwo : Tendsto (deriv (deriv g)) (𝓝[>] 0)
      (𝓝 (hessianMatrix (radialExtension 9 f) 0 0 0)) := by
    simpa only [hsecond] using hg2.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hquot : Tendsto (fun r => deriv g r / r) (𝓝[>] 0)
      (𝓝 (hessianMatrix (radialExtension 9 f) 0 0 0)) := by
    simpa only [zero_add, heven, sub_zero, smul_eq_mul, hsecond, div_eq_mul_inv,
      mul_comm] using hg1.differentiableAt_one.hasDerivAt.tendsto_slope_zero_right
  refine ⟨hzero.congr' hge.symm, hone.congr' hde.symm, htwo.congr' hdde.symm, ?_⟩
  apply hquot.congr'
  filter_upwards [hde] with r hr
  rw [hr]

-- @node: lem:autonomous
/-- Given [normalized local radial solution data F₀ and P₀ on radius ε](hyp:hLocal)
and [a maximal positive continuation F and P up to R](hyp:hCont), [the radial
coordinates are well-defined with positive first two components throughout the
continuation interval and solve the autonomous equation in logarithmic radius;
as the radius decreases to zero they tend to (0, 1, 0), and all three components
are strictly positive for every sufficiently small positive radius](goal). -/
lemma autonomous_system_of_continuation {ε : ℝ} {F₀ P₀ F P : ℝ → ℝ}
    {R : WithTop ℝ} (hLocal : LocalSolutionData ε F₀ P₀)
    (hCont : IsMaximalContinuation F₀ P₀ ε F P R) :
    (∀ r ∈ radialInterval R,
      RadialCoordinateDomain F P r ∧
      0 < radialCoordinates F P r 0 ∧ 0 < radialCoordinates F P r 1 ∧
      HasDerivAt (fun τ => radialCoordinates F P (Real.exp τ))
        (autonomousField (radialCoordinates F P r)) (Real.log r)) ∧
    Tendsto (radialCoordinates F P) (𝓝[>] 0) (𝓝 (![0, 1, 0] : Fin 3 → ℝ)) ∧
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      0 < radialCoordinates F P r 0 ∧ 0 < radialCoordinates F P r 1 ∧
        0 < radialCoordinates F P r 2 := by
  have hSol := hCont.2.2.2.1
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 ε := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hLocal.1).filter_mono nhdsWithin_le_nhds] with r hr hε
    exact ⟨hr, hε⟩
  have hinterval : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ radialInterval R := by
    filter_upwards [hsmall] with r hr
    exact ⟨hr.1, lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hr.2) hCont.2.1⟩
  have heqF (r : ℝ) (hr : r ∈ Ioo 0 ε) : F =ᶠ[𝓝 r] F₀ := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    exact (hCont.2.2.1 s ⟨hs.1.le, hs.2⟩).1
  have heqP (r : ℝ) (hr : r ∈ Ioo 0 ε) : P =ᶠ[𝓝 r] P₀ := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    exact (hCont.2.2.1 s ⟨hs.1.le, hs.2⟩).2
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      F r = F₀ r ∧ P r = P₀ r ∧ deriv F r = deriv F₀ r ∧
        deriv (deriv F) r = deriv (deriv F₀) r ∧ deriv P r = deriv P₀ r := by
    filter_upwards [hsmall] with r hr
    exact ⟨(heqF r hr).eq_of_nhds, (heqP r hr).eq_of_nhds,
      (heqF r hr).deriv_eq, (heqF r hr).deriv.deriv_eq, (heqP r hr).deriv_eq⟩
  obtain ⟨hF₀, hy₀, hyy₀, hquot₀⟩ :=
    radial_profile_origin_limits hLocal.1 hLocal.2.2.1
  obtain ⟨hP₀, hz₀, _, _⟩ :=
    radial_profile_origin_limits hLocal.1 hLocal.2.2.2.1
  have hFn : F₀ 0 = 1 := hLocal.2.2.2.2.1
  have hPn : P₀ 0 = 1 := hLocal.2.2.2.2.2.1
  have hHn : hessianMatrix (radialExtension 9 F₀) 0 0 0 = 1 := by
    rw [hLocal.2.2.2.2.2.2.1]
    simp
  rw [hFn] at hF₀
  rw [hPn] at hP₀
  rw [hHn] at hyy₀ hquot₀
  have hF : Tendsto F (𝓝[>] 0) (𝓝 1) := by
    apply hF₀.congr'
    filter_upwards [heq] with r hr using hr.1.symm
  have hP : Tendsto P (𝓝[>] 0) (𝓝 1) := by
    apply hP₀.congr'
    filter_upwards [heq] with r hr using hr.2.1.symm
  have hy : Tendsto (deriv F) (𝓝[>] 0) (𝓝 0) := by
    apply hy₀.congr'
    filter_upwards [heq] with r hr using hr.2.2.1.symm
  have hz : Tendsto (deriv P) (𝓝[>] 0) (𝓝 0) := by
    apply hz₀.congr'
    filter_upwards [heq] with r hr using hr.2.2.2.2.symm
  have hyy : Tendsto (deriv (deriv F)) (𝓝[>] 0) (𝓝 1) := by
    apply hyy₀.congr'
    filter_upwards [heq] with r hr using hr.2.2.2.1.symm
  have hquot : Tendsto (fun r => deriv F r / r) (𝓝[>] 0) (𝓝 1) := by
    apply hquot₀.congr'
    filter_upwards [heq] with r hr
    rw [hr.2.2.1]
  have hid : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun r => r * deriv F r / F r) (𝓝[>] 0) (𝓝 0) := by
    simpa [Pi.div_def] using (hid.mul hy).div hF (by norm_num)
  have hB : Tendsto (fun r => r * deriv (deriv F) r / deriv F r)
      (𝓝[>] 0) (𝓝 1) := by
    have hh := hyy.div hquot (by norm_num : (1 : ℝ) ≠ 0)
    simpa [Pi.div_def, div_div_eq_mul_div, mul_comm] using hh
  have hC : Tendsto (fun r => -(r * deriv P r / P r)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((hid.mul hz).div hP (by norm_num)).neg
  have hD := hC.div hB (by norm_num : (1 : ℝ) ≠ 0)
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    have hp := radial_coordinates_first_two_pos hSol hr
    exact ⟨radial_coordinate_domain_of_positive hSol hr, hp.1, hp.2,
      radial_coordinates_log_derivative hSol hr⟩
  · have hv : Tendsto
        (fun r => ![r * deriv F r / F r, r * deriv (deriv F) r / deriv F r,
          (-(r * deriv P r / P r)) / (r * deriv (deriv F) r / deriv F r)])
        (𝓝[>] 0) (𝓝 (![0, 1, 0] : Fin 3 → ℝ)) := by
      apply tendsto_pi_nhds.mpr
      intro i
      fin_cases i
      · simpa using hA
      · simpa using hB
      · simpa [Pi.div_def] using hD
    apply hv.congr'
    filter_upwards [hinterval] with r hr
    exact (radialCoordinates_eq_of_domain (radial_coordinate_domain_of_positive hSol hr)).symm
  · filter_upwards [hsmall, hinterval, heq] with r hr hri he
    have hd := radial_coordinate_domain_of_positive hSol hri
    have hp := radial_coordinates_first_two_pos hSol hri
    refine ⟨hp.1, hp.2, ?_⟩
    rw [radialCoordinates_eq_of_domain hd]
    simp only [Matrix.cons_val_two]
    apply div_pos _ hd.2.2.2.2
    apply neg_pos.mpr
    apply div_neg_of_neg_of_pos _ (hSol.2.2 r hri).2.1
    apply mul_neg_of_pos_of_neg hr.1
    rw [he.2.2.2.2]
    exact (hLocal.2.2.2.2.2.2.2.2 r hr).2.2.2.2


end OaiSmoothNonquadraticAffine
