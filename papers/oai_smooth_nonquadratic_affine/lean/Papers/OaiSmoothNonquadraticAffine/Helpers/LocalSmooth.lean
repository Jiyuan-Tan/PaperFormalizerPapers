module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.LocalOrigin
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Smoothness bootstrap for the local integral fixed point

Weighted averages preserve each finite differentiability order. Differentiating
an average increases its weight by two, so the primitive equations can be
bootstrapped without a loss of derivatives at the auxiliary origin.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace OaiSmoothNonquadraticAffine

-- @node: localAverage_scale_abs_le
/-- If [v lies between zero and one, inclusive](hyp:hv), then [multiplying any
real s by v² cannot increase its absolute value](goal). -/
lemma localAverage_scale_abs_le {v s : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    |v ^ 2 * s| ≤ |s| := by
  rw [abs_mul, abs_of_nonneg (sq_nonneg v)]
  exact mul_le_of_le_one_left (abs_nonneg s) (by nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hv.2)])

-- @node: localAverage_scale_mem
/-- If [v lies between zero and one, inclusive](hyp:hv), and [s lies strictly
between −δ and δ](hyp:hs), then [v²s also lies strictly between −δ and δ](goal). -/
lemma localAverage_scale_mem {δ v s : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Ioo (-δ) δ) : v ^ 2 * s ∈ Ioo (-δ) δ := by
  exact abs_lt.mp ((localAverage_scale_abs_le hv).trans_lt (abs_lt.mpr hs))

-- @node: localWeightedAverage_integrand_continuousOn
/-- For [a real function h](hyp:h) [continuous on the open interval from −δ
to δ](hyp:hc), if [s lies in that interval](hyp:hs), then [the weighted
integrand vᴺh(v²s) is continuous for v between zero and one, inclusive, for
every nonnegative integer N](goal). -/
@[fun_prop] lemma localWeightedAverage_integrand_continuousOn {δ : ℝ} {h : ℝ → ℝ}
    (hc : ContinuousOn h (Ioo (-δ) δ)) (N : ℕ) {s : ℝ} (hs : s ∈ Ioo (-δ) δ) :
    ContinuousOn (fun v : ℝ => v ^ N * h (v ^ 2 * s)) (Icc 0 1) := by
  apply ContinuousOn.mul (by fun_prop)
  exact hc.comp (by fun_prop) (fun v hv => localAverage_scale_mem hv hs)

-- @node: localWeightedAverage_continuousOn
/-- For [a real function h](hyp:h) [continuous on the open interval from −δ
to δ](hyp:hc), [the integral of vᴺh(v²s) from zero to one is continuous as a
function of s on that interval, for every nonnegative integer N](goal). -/
@[fun_prop] lemma localWeightedAverage_continuousOn {δ : ℝ} {h : ℝ → ℝ}
    (hc : ContinuousOn h (Ioo (-δ) δ)) (N : ℕ) :
    ContinuousOn (fun s : ℝ => ∫ v : ℝ in 0..1, v ^ N * h (v ^ 2 * s))
      (Ioo (-δ) δ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hj : Continuous (fun z : Ioo (-δ) δ × ℝ =>
      z.2 ^ N * h ((projIcc 0 1 (by norm_num) z.2 : ℝ) ^ 2 * z.1)) := by
    apply Continuous.mul (by fun_prop)
    apply hc.comp_continuous (by fun_prop)
    intro z
    exact localAverage_scale_mem (projIcc 0 1 (by norm_num) z.2).property z.1.property
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun s : Ioo (-δ) δ => fun v : ℝ =>
      v ^ N * h ((projIcc 0 1 (by norm_num) v : ℝ) ^ 2 * s)) hj 0 1
  apply hi.congr
  intro s
  apply intervalIntegral.integral_congr
  intro v hv
  dsimp only
  rw [projIcc_of_mem _ (by simpa using hv)]

-- @node: localWeightedAverage_hasDerivAt
/-- For [a real function h](hyp:h) [continuously differentiable on the open
interval from −δ to δ](hyp:hc), and [s in that interval](hyp:hs), [the
derivative at s of the integral of vᴺh(v²s) from zero to one equals the
integral of v to the power N+2 times h′(v²s) over the same interval](goal). -/
lemma localWeightedAverage_hasDerivAt {δ : ℝ} {h : ℝ → ℝ}
    (hc : ContDiffOn ℝ 1 h (Ioo (-δ) δ)) (N : ℕ) {s : ℝ}
    (hs : s ∈ Ioo (-δ) δ) :
    HasDerivAt (fun a : ℝ => ∫ v : ℝ in 0..1, v ^ N * h (v ^ 2 * a))
      (∫ v : ℝ in 0..1, v ^ (N + 2) * deriv h (v ^ 2 * s)) s := by
  have hsabs : |s| < δ := abs_lt.mpr hs
  obtain ⟨a, hsa, haδ⟩ := exists_between hsabs
  have ha : 0 < a := (abs_nonneg s).trans_lt hsa
  have hsub : Icc (-a) a ⊆ Ioo (-δ) δ := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hd : ContinuousOn (deriv h) (Ioo (-δ) δ) :=
    hc.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hd.mono hsub)
  have hneigh : Ioo (-a) a ∈ 𝓝 s := isOpen_Ioo.mem_nhds (abs_lt.mp hsa)
  have hmeas : ∀ᶠ x in 𝓝 s, AEStronglyMeasurable
      (fun v : ℝ => v ^ N * h (v ^ 2 * x)) (volume.restrict (uIoc 0 1)) := by
    filter_upwards [hneigh] with x hx
    simpa using ((localWeightedAverage_integrand_continuousOn hc.continuousOn N
      (hsub ⟨hx.1.le, hx.2.le⟩)).intervalIntegrable_of_Icc (μ := volume)
        (by norm_num)).1.aestronglyMeasurable
  have hint : IntervalIntegrable (fun v : ℝ => v ^ N * h (v ^ 2 * s)) volume 0 1 :=
    (localWeightedAverage_integrand_continuousOn hc.continuousOn N hs).intervalIntegrable_of_Icc
      (by norm_num)
  have hmeas' : AEStronglyMeasurable
      (fun v : ℝ => v ^ (N + 2) * deriv h (v ^ 2 * s))
      (volume.restrict (uIoc 0 1)) := by
    simpa using ((localWeightedAverage_integrand_continuousOn hd
      (N + 2) hs).intervalIntegrable_of_Icc (μ := volume) (by norm_num)).1.aestronglyMeasurable
  have hbound : ∀ᵐ v : ℝ ∂volume, v ∈ uIoc (0 : ℝ) 1 →
      ∀ x ∈ Ioo (-a) a, ‖v ^ (N + 2) * deriv h (v ^ 2 * x)‖ ≤ M := by
    filter_upwards [] with v hv x hx
    have hv' : v ∈ Icc (0 : ℝ) 1 := by
      have hv'' : v ∈ Ioc (0 : ℝ) 1 := by simpa using hv
      exact ⟨hv''.1.le, hv''.2⟩
    have hx' : v ^ 2 * x ∈ Icc (-a) a :=
      abs_le.mp ((localAverage_scale_abs_le hv').trans (abs_le.mpr ⟨hx.1.le, hx.2.le⟩))
    rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hv'.1 _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hv'.1 hv'.2)).trans (hM _ hx')
  have hdiff : ∀ᵐ v : ℝ ∂volume, v ∈ uIoc (0 : ℝ) 1 → ∀ x ∈ Ioo (-a) a,
      HasDerivAt (fun x : ℝ => v ^ N * h (v ^ 2 * x))
        (v ^ (N + 2) * deriv h (v ^ 2 * x)) x := by
    filter_upwards [] with v hv x hx
    have hv' : v ∈ Icc (0 : ℝ) 1 := by
      have hv'' : v ∈ Ioc (0 : ℝ) 1 := by simpa using hv
      exact ⟨hv''.1.le, hv''.2⟩
    have hpoint := localAverage_scale_mem hv' (hsub ⟨hx.1.le, hx.2.le⟩)
    have hh := (hc.contDiffAt (isOpen_Ioo.mem_nhds hpoint)).differentiableAt (by norm_num)
    convert (hh.hasDerivAt.comp x ((hasDerivAt_id x).const_mul (v ^ 2))).const_mul
      (v ^ N) using 1 <;> first | rfl | (simp only [pow_add]; ring)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hneigh hmeas hint hmeas' hbound (intervalIntegrable_const)
    hdiff).2

-- @node: localWeightedAverage_contDiffOn
/-- For [a real function h](hyp:h) [with n continuous derivatives on the open
interval from −δ to δ](hyp:hc), [the integral of vᴺh(v²s) from zero to one
also has n continuous derivatives as a function of s on that interval, for
every nonnegative integer weight N](goal). -/
lemma localWeightedAverage_contDiffOn {δ : ℝ} (n : ℕ) {h : ℝ → ℝ}
    (hc : ContDiffOn ℝ n h (Ioo (-δ) δ)) (N : ℕ) :
    ContDiffOn ℝ n (fun s : ℝ => ∫ v : ℝ in 0..1, v ^ N * h (v ^ 2 * s))
      (Ioo (-δ) δ) := by
  induction n generalizing h N with
  | zero => exact contDiffOn_zero.mpr (localWeightedAverage_continuousOn hc.continuousOn N)
  | succ n ih =>
    have h1 : ContDiffOn ℝ 1 h (Ioo (-δ) δ) := hc.of_le (by norm_cast; omega)
    have hder := fun s hs => localWeightedAverage_hasDerivAt h1 N (s := s) hs
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun s hs => (hder s hs).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    apply (ih (hc.deriv_of_isOpen isOpen_Ioo (by simp)) (N + 2)).congr
    intro s hs
    exact (hder s hs).deriv

-- @node: localFixedPoint_extensions_contDiffOn
/-- If [δ is positive](hyp:hδ), [the trial pair is admissible](hyp:hfp) and
[is a fixed point of the local transform](hyp:hfix), and [the first integral
primitive](hyp:hf) and [the second integral primitive](hyp:hp) each have
continuous derivatives through order n on the open interval from −δ to δ,
then [both extended trial profiles have continuous derivatives through order
n on that interval](goal). -/
lemma localFixedPoint_extensions_contDiffOn {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ)
    (hfix : ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s)
    {n : ℕ∞ω}
    (hf : ContDiffOn ℝ n (fun s => (localIntegralPrimitives hδ fp hfp s).1) (Ioo (-δ) δ))
    (hp : ContDiffOn ℝ n (fun s => (localIntegralPrimitives hδ fp hfp s).2) (Ioo (-δ) δ)) :
    ContDiffOn ℝ n (localTrialExtension δ hδ fp.1) (Ioo (-δ) δ) ∧
    ContDiffOn ℝ n (localTrialExtension δ hδ fp.2) (Ioo (-δ) δ) := by
  constructor
  · apply hf.congr
    intro s hs
    exact congrArg Prod.fst (localFixedPoint_extension_eq hδ hfp hfix ⟨s, hs.1.le, hs.2.le⟩)
  · apply hp.congr
    intro s hs
    exact congrArg Prod.snd (localFixedPoint_extension_eq hδ hfp hfix ⟨s, hs.1.le, hs.2.le⟩)

-- @node: localAverages_contDiffOn
/-- For [positive δ](hyp:hδ) and [an admissible trial pair](hyp:hfp), if [the
first extended trial profile has n continuous derivatives on the open interval
from −δ to δ](hyp:hf) and [the second extended trial profile does too](hyp:hp),
then [both normalized factors Q and J have n continuous derivatives on that
interval](goal). -/
lemma localAverages_contDiffOn {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (n : ℕ)
    (hf : ContDiffOn ℝ n (localTrialExtension δ hδ fp.1) (Ioo (-δ) δ))
    (hp : ContDiffOn ℝ n (localTrialExtension δ hδ fp.2) (Ioo (-δ) δ)) :
    ContDiffOn ℝ n (localQ δ hδ fp hfp) (Ioo (-δ) δ) ∧
    ContDiffOn ℝ n (localJ δ hδ fp hfp) (Ioo (-δ) δ) := by
  have hpne : ∀ s ∈ Ioo (-δ) δ, localTrialExtension δ hδ fp.2 s ≠ 0 := by
    intro s _
    linarith [(localTrialExtension_mem hδ hfp s).2.1]
  have hq := localWeightedAverage_contDiffOn n
    (hf.mul (hp.rpow_const_of_ne (p := -radialGamma) hpne)) 8
  have hj := localWeightedAverage_contDiffOn n
    (hp.rpow_const_of_ne (p := 1 - radialGamma) hpne) 8
  refine ⟨?_, hj⟩
  have hroot : ContDiffOn ℝ n (fun s => 9 * ∫ v : ℝ in 0..1,
      v ^ 8 * localTrialExtension δ hδ fp.1 (v ^ 2 * s) *
        localTrialExtension δ hδ fp.2 (v ^ 2 * s) ^ (-radialGamma)) (Ioo (-δ) δ) := by
    simpa only [mul_assoc] using (contDiffOn_const.mul hq : ContDiffOn ℝ n
      (fun s => 9 * ∫ v : ℝ in 0..1, v ^ 8 *
        (localTrialExtension δ hδ fp.1 (v ^ 2 * s) *
          localTrialExtension δ hδ fp.2 (v ^ 2 * s) ^ (-radialGamma))) (Ioo (-δ) δ))
  exact hroot.rpow_const_of_ne (fun s _ =>
    (mul_pos (by norm_num) (localAverage_pos hδ hfp (-radialGamma) s)).ne')

-- @node: localIntegralPrimitives_contDiffOn_nat
/-- If [δ is positive](hyp:hδ), [the trial pair is admissible](hyp:hfp) and
[is a fixed point of the local transform](hyp:hfix), then [both integral
primitives have n continuous derivatives on the open interval from −δ to δ,
for every nonnegative integer n](goal). -/
lemma localIntegralPrimitives_contDiffOn_nat {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ)
    (hfix : ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s) (n : ℕ) :
    ContDiffOn ℝ n (fun s => (localIntegralPrimitives hδ fp hfp s).1) (Ioo (-δ) δ) ∧
    ContDiffOn ℝ n (fun s => (localIntegralPrimitives hδ fp hfp s).2) (Ioo (-δ) δ) := by
  have hd := localIntegralPrimitives_hasDerivAt hδ hfp
  induction n with
  | zero =>
    have hc := localIntegralPrimitives_contDiff_one hδ hfp
    exact ⟨(hc.1.of_le (by norm_num)).contDiffOn, (hc.2.of_le (by norm_num)).contDiffOn⟩
  | succ n ih =>
    have he := localFixedPoint_extensions_contDiffOn hδ hfp hfix ih.1 ih.2
    obtain ⟨hq, hj⟩ := localAverages_contDiffOn hδ hfp n he.1 he.2
    have hdp : ContDiffOn ℝ n (fun s => (localDifferentialValues hδ fp hfp s).2)
        (Ioo (-δ) δ) :=
      (contDiffOn_const.mul hj).mul (hq.rpow_const_of_ne (fun s _ => (localQ_pos hδ hfp s).ne'))
    have lift (f d : ℝ → ℝ) (hfd : ∀ s, HasDerivAt f (d s) s)
        (hc : ContDiffOn ℝ n d (Ioo (-δ) δ)) :
        ContDiffOn ℝ (n + 1) f (Ioo (-δ) δ) := by
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨fun s _ => (hfd s).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact hc.congr (fun s _ => (hfd s).deriv)
    exact ⟨lift _ _ (fun s => (hd s).1) hq, lift _ _ (fun s => (hd s).2) hdp⟩

-- @node: localIntegralPrimitives_contDiffOn
/-- If [δ is positive](hyp:hδ), [the trial pair is admissible](hyp:hfp) and
[is a fixed point of the local transform](hyp:hfix), then [both integral
primitives are infinitely differentiable on the open interval from −δ to
δ](goal). -/
lemma localIntegralPrimitives_contDiffOn {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ)
    (hfix : ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s) :
    ContDiffOn ℝ ∞ (fun s => (localIntegralPrimitives hδ fp hfp s).1) (Ioo (-δ) δ) ∧
    ContDiffOn ℝ ∞ (fun s => (localIntegralPrimitives hδ fp hfp s).2) (Ioo (-δ) δ) := by
  exact ⟨contDiffOn_infty.mpr (fun n =>
      (localIntegralPrimitives_contDiffOn_nat hδ hfp hfix n).1),
    contDiffOn_infty.mpr (fun n => (localIntegralPrimitives_contDiffOn_nat hδ hfp hfix n).2)⟩

end OaiSmoothNonquadraticAffine
