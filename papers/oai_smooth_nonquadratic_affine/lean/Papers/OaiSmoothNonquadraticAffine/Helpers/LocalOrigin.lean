module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.LocalRadial
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Asymptotics

/-! # The Hessians at the origin of the local radial construction

Only continuity of the auxiliary first derivatives is needed here: the
vanishing spatial linear factor supplies the derivative at the origin.
-/

public section

open Set Filter Asymptotics
open scoped Topology ContDiff

namespace OaiSmoothNonquadraticAffine

-- @node: localIntegralPrimitives_contDiff_one
/-- If [δ is positive](hyp:hδ) and [both trial components stay within one half
of one](hyp:hfp), [both local integral primitives are continuously
differentiable on the real auxiliary line](goal). -/
lemma localIntegralPrimitives_contDiff_one {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) :
    ContDiff ℝ 1 (fun s => (localIntegralPrimitives hδ fp hfp s).1) ∧
    ContDiff ℝ 1 (fun s => (localIntegralPrimitives hδ fp hfp s).2) := by
  have hd := localIntegralPrimitives_hasDerivAt hδ hfp
  have hc := localDifferentialValues_continuous hδ hfp
  constructor
  · apply contDiff_one_iff_deriv.mpr
    refine ⟨fun s => (hd s).1.differentiableAt, ?_⟩
    have he := funext (fun s => (hd s).1.deriv)
    rw [he]
    exact hc.fst
  · apply contDiff_one_iff_deriv.mpr
    refine ⟨fun s => (hd s).2.differentiableAt, ?_⟩
    have he := funext (fun s => (hd s).2.deriv)
    rw [he]
    exact hc.snd

-- @node: localRadialProfiles_spatial_contDiff_one
/-- If [δ is positive](hyp:hδ) and [both trial components stay within one half
of one](hyp:hfp), [the spatial extensions of both local radial profiles are
continuously differentiable on nine-dimensional Euclidean space](goal). -/
lemma localRadialProfiles_spatial_contDiff_one {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) :
    ContDiff ℝ 1
      (radialExtension 9 (fun r => (localRadialProfiles hδ fp hfp r).1)) ∧
    ContDiff ℝ 1
      (radialExtension 9 (fun r => (localRadialProfiles hδ fp hfp r).2)) := by
  have hc := localIntegralPrimitives_contDiff_one hδ hfp
  have hs : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 9) => ‖x‖ ^ 2 / 2) := by
    exact (contDiff_norm_sq ℝ).div_const 2
  exact ⟨hc.1.comp hs, hc.2.comp hs⟩

-- @node: localRadialProfiles_spatial_contDiffOn
/-- If [δ is positive](hyp:hδ), [both trial components stay within one half
of one](hyp:hfp), [the first integral primitive has continuous derivatives
through order n on the open interval from −δ to δ](hyp:hf), and [the second
integral primitive has the same regularity there](hyp:hp), [both spatial radial
extensions have continuous derivatives through order n on the open ball
centered at zero with radius the smaller of δ and one in nine-dimensional
Euclidean space](goal). -/
lemma localRadialProfiles_spatial_contDiffOn {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) {n : ℕ∞ω}
    (hf : ContDiffOn ℝ n (fun s => (localIntegralPrimitives hδ fp hfp s).1) (Ioo (-δ) δ))
    (hp : ContDiffOn ℝ n (fun s => (localIntegralPrimitives hδ fp hfp s).2) (Ioo (-δ) δ)) :
    ContDiffOn ℝ n
      (radialExtension 9 (fun r => (localRadialProfiles hδ fp hfp r).1))
      (Metric.ball 0 (min δ 1)) ∧
    ContDiffOn ℝ n
      (radialExtension 9 (fun r => (localRadialProfiles hδ fp hfp r).2))
      (Metric.ball 0 (min δ 1)) := by
  have hs : ContDiffOn ℝ n (fun x : EuclideanSpace ℝ (Fin 9) => ‖x‖ ^ 2 / 2)
      (Metric.ball 0 (min δ 1)) := ((contDiff_norm_sq ℝ).div_const 2).contDiffOn
  have hm : MapsTo (fun x : EuclideanSpace ℝ (Fin 9) => ‖x‖ ^ 2 / 2)
      (Metric.ball 0 (min δ 1)) (Ioo (-δ) δ) := by
    intro x hx
    have hx' : ‖x‖ < min δ 1 := by simpa using hx
    have hxδ := hx'.trans_le (min_le_left δ 1)
    have hx1 := hx'.trans_le (min_le_right δ 1)
    constructor
    · nlinarith [sq_nonneg ‖x‖]
    · nlinarith [norm_nonneg x, mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hx1.le)]
  exact ⟨hf.comp hs hm, hp.comp hs hm⟩

-- @node: localOrigin_continuous_mul_linear
/-- If [a real-valued function g on a real normed vector space is continuous
at zero](hyp:hg), [the product of g with any continuous linear functional L
is differentiable at zero, with derivative equal to L multiplied by the
value of g at zero](goal). -/
lemma localOrigin_continuous_mul_linear {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : E → ℝ} (hg : ContinuousAt g 0) (L : E →L[ℝ] ℝ) :
    HasFDerivAt (fun x => g x * L x) (g 0 • L) 0 := by
  have hsmall : (fun x => g x - g 0) =o[𝓝 0] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (by
      simpa using hg.tendsto.sub (tendsto_const_nhds (x := g 0)))
  have hprod := hsmall.mul_isBigO (L.isBigO_id (𝓝 0)).norm_right
  simp only [one_mul] at hprod
  apply HasFDerivAt.of_isLittleO
  simpa only [map_zero, mul_zero, sub_zero, smul_apply,
    smul_eq_mul, ← sub_mul, one_mul] using hprod.of_norm_right

-- @node: localOrigin_auxiliary_hasFDerivAt
/-- [At every point x in n-dimensional Euclidean space, one half of the squared
norm is differentiable, with derivative sending a direction v to the inner
product of x and v](goal). -/
lemma localOrigin_auxiliary_hasFDerivAt {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2 / 2)
      (innerSL ℝ x) x := by
  have hd := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.mul_const (1 / 2 : ℝ)
  have he : (1 / 2 : ℝ) • (2 • innerSL ℝ x) = innerSL ℝ x := by
    ext v
    simp
  rw [he] at hd
  simpa [div_eq_mul_inv] using hd

-- @node: localOrigin_composition_fderiv
/-- If [the real function f has derivative d at every real argument](hyp:hd),
[the derivative at any point x of f evaluated at one half of the squared norm
sends a direction v to the inner product of x and v multiplied by d evaluated
at one half of the squared norm of x](goal). -/
lemma localOrigin_composition_fderiv {n : ℕ} {f d : ℝ → ℝ}
    (hd : ∀ s, HasDerivAt f (d s) s) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => f (‖y‖ ^ 2 / 2)) x =
      d (‖x‖ ^ 2 / 2) • innerSL ℝ x := by
  exact ((hd _).comp_hasFDerivAt x (localOrigin_auxiliary_hasFDerivAt x)).fderiv

-- @node: localOrigin_composition_hessian
/-- If [the real function f has derivative d at every real argument](hyp:hd)
and [d is continuous at zero](hyp:hc), [the Hessian at the origin of f evaluated
at one half of the squared Euclidean norm is the identity matrix multiplied
by the value of d at zero](goal). -/
lemma localOrigin_composition_hessian {n : ℕ} {f d : ℝ → ℝ}
    (hd : ∀ s, HasDerivAt f (d s) s) (hc : ContinuousAt d 0) :
    hessianMatrix (fun x : EuclideanSpace ℝ (Fin n) => f (‖x‖ ^ 2 / 2)) 0 =
      d 0 • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hcont : ContinuousAt (fun x : EuclideanSpace ℝ (Fin n) => d (‖x‖ ^ 2 / 2)) 0 := by
    exact hc.comp_of_eq (show ContinuousAt
      (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 / 2) 0 by fun_prop) (by simp)
  ext i j
  simp only [hessianMatrix, localOrigin_composition_fderiv hd,
    smul_apply, smul_eq_mul, innerSL_apply_apply]
  have he : (fun y : EuclideanSpace ℝ (Fin n) =>
      d (‖y‖ ^ 2 / 2) * inner ℝ y (EuclideanSpace.single j 1)) =
      (fun y => d (‖y‖ ^ 2 / 2) * innerSL ℝ (EuclideanSpace.single j 1) y) := by
    ext y
    simp [real_inner_comm]
  rw [he, (localOrigin_continuous_mul_linear hcont _).fderiv]
  simp [EuclideanSpace.inner_single_left, PiLp.single_apply, Matrix.one_apply, eq_comm]

-- @node: localRadialProfiles_hessians_zero
/-- If [δ is positive](hyp:hδ), [both trial components stay within one half
of one](hyp:hfp), and [the trial pair equals its local integral transform at
every point of the interval](hyp:hfix), [the Hessians at the origin of the
two spatial radial profiles in nine dimensions are respectively the identity
matrix and the identity matrix multiplied by −11/9](goal). -/
lemma localRadialProfiles_hessians_zero {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ)
    (hfix : ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s) :
    hessianMatrix (radialExtension 9 (fun r => (localRadialProfiles hδ fp hfp r).1)) 0 = 1 ∧
    hessianMatrix (radialExtension 9 (fun r => (localRadialProfiles hδ fp hfp r).2)) 0 =
      -(11 / 9 : ℝ) • (1 : Matrix (Fin 9) (Fin 9) ℝ) := by
  have hc := localDifferentialValues_continuous hδ hfp
  have hd := localIntegralPrimitives_hasDerivAt hδ hfp
  have hi := localFixedPoint_initial_derivatives hδ hfp hfix
  have hF := (hd 0).1.unique hi.1
  have hP := (hd 0).2.unique hi.2
  constructor
  · change hessianMatrix (fun x : EuclideanSpace ℝ (Fin 9) =>
      (localIntegralPrimitives hδ fp hfp (‖x‖ ^ 2 / 2)).1) 0 = 1
    rw [localOrigin_composition_hessian (fun s => (hd s).1) hc.fst.continuousAt, hF,
      one_smul]
  · change hessianMatrix (fun x : EuclideanSpace ℝ (Fin 9) =>
      (localIntegralPrimitives hδ fp hfp (‖x‖ ^ 2 / 2)).2) 0 = _
    rw [localOrigin_composition_hessian (fun s => (hd s).2) hc.snd.continuousAt, hP]

end OaiSmoothNonquadraticAffine
