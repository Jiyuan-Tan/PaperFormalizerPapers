module

public import Papers.OaiSmoothNonquadraticAffine.Helpers.LocalConstructions
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Analytic foundations for the local fixed-point construction

The averages are continuous and strictly positive on the whole auxiliary line.
The final fixed-point lemma isolates the Banach step from the uniform estimates;
it does not assert those estimates or the smoothness bootstrap.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped Topology NNReal

namespace OaiSmoothNonquadraticAffine

-- @node: localTrialSet_isClosed
/-- [The set of continuous trial pairs on the interval from −δ to δ whose
components stay within one half of one is closed](goal). -/
lemma localTrialSet_isClosed (δ : ℝ) : IsClosed (localTrialSet δ) := by
  change IsClosed {fp : LocalTrialPair δ |
    (∀ s, |fp.1 s - 1| ≤ 1 / 2) ∧ (∀ s, |fp.2 s - 1| ≤ 1 / 2)}
  apply IsClosed.inter
  · convert (isClosed_iInter fun s : Icc (-δ) δ => isClosed_le
      (show Continuous (fun fp : LocalTrialPair δ => |fp.1 s - 1|) by fun_prop)
      (continuous_const : Continuous (fun _ : LocalTrialPair δ => (1 / 2 : ℝ)))) using 1
    apply Iff.of_eq
    congr 1
    ext fp
    simp
    rfl
  · convert (isClosed_iInter fun s : Icc (-δ) δ => isClosed_le
      (show Continuous (fun fp : LocalTrialPair δ => |fp.2 s - 1|) by fun_prop)
      (continuous_const : Continuous (fun _ : LocalTrialPair δ => (1 / 2 : ℝ)))) using 1
    apply Iff.of_eq
    congr 1
    ext fp
    simp
    rfl

-- @node: localTrialSet_nonempty
/-- [There exists a continuous trial pair on the interval from −δ to δ whose
components stay within one half of one](goal). -/
lemma localTrialSet_nonempty (δ : ℝ) : (localTrialSet δ).Nonempty := by
  refine ⟨(ContinuousMap.const _ 1, ContinuousMap.const _ 1), ?_⟩
  constructor <;> intro s <;> norm_num

-- @node: localTrialExtension_continuous
/-- If [the interval half-width δ is positive](hyp:hδ), [extending a continuous
function on the interval from −δ to δ by constant endpoint values gives a
continuous function on the whole real line](goal). -/
@[fun_prop] lemma localTrialExtension_continuous (δ : ℝ) (hδ : 0 < δ)
    (f : C(Icc (-δ) δ, ℝ)) : Continuous (localTrialExtension δ hδ f) := by
  unfold localTrialExtension
  fun_prop

-- @node: localTrialExtension_mem
/-- If [δ is positive](hyp:hδ) and [both trial components stay within one half
of one on the interval from −δ to δ](hyp:hfp), [their constant-endpoint
extensions both lie between one half and three halves at every real point s](goal). -/
lemma localTrialExtension_mem {δ : ℝ} (hδ : 0 < δ) {fp : LocalTrialPair δ}
    (hfp : fp ∈ localTrialSet δ) (s : ℝ) :
    localTrialExtension δ hδ fp.1 s ∈ Icc (1 / 2 : ℝ) (3 / 2) ∧
    localTrialExtension δ hδ fp.2 s ∈ Icc (1 / 2 : ℝ) (3 / 2) := by
  have hf := abs_le.mp (hfp.1 (projIcc (-δ) δ (neg_le_self hδ.le) s))
  have hp := abs_le.mp (hfp.2 (projIcc (-δ) δ (neg_le_self hδ.le) s))
  dsimp [localTrialExtension]
  constructor <;> constructor <;> linarith

-- @node: localTrialExtension_eq
/-- If [δ is positive](hyp:hδ), [the constant-endpoint extension of a continuous
function on the interval from −δ to δ agrees with that function at every point
s of the interval](goal). -/
lemma localTrialExtension_eq {δ : ℝ} (hδ : 0 < δ)
    (f : C(Icc (-δ) δ, ℝ)) (s : Icc (-δ) δ) :
    localTrialExtension δ hδ f s = f s := by
  unfold localTrialExtension
  rw [projIcc_of_mem _ s.property]

-- @node: localAverage_integrand_continuous
/-- If [δ is positive](hyp:hδ) and [both trial components stay within one half
of one](hyp:hfp), [the slope-average integrand is jointly continuous in the
real variables s and v for every real exponent α: it is v to the eighth power
times the extended first component at v²s times the extended second component
at v²s raised to α](goal). -/
@[fun_prop] lemma localAverage_integrand_continuous {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (α : ℝ) :
    Continuous (fun z : ℝ × ℝ => z.2 ^ 8 *
      localTrialExtension δ hδ fp.1 (z.2 ^ 2 * z.1) *
      localTrialExtension δ hδ fp.2 (z.2 ^ 2 * z.1) ^ α) := by
  have hp : Continuous (fun z : ℝ × ℝ =>
      localTrialExtension δ hδ fp.2 (z.2 ^ 2 * z.1) ^ α) :=
    (show Continuous (fun z : ℝ × ℝ =>
      localTrialExtension δ hδ fp.2 (z.2 ^ 2 * z.1)) by fun_prop).rpow_const
        (fun z => Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
          (localTrialExtension_mem hδ hfp _).2.1)))
  fun_prop

-- @node: localFlux_integrand_continuous
/-- If [δ is positive](hyp:hδ) and [both trial components stay within one half
of one](hyp:hfp), [the flux integrand is jointly continuous in the real variables
s and v for every real exponent α: it is v to the eighth power times the
extended second component at v²s raised to α](goal). -/
@[fun_prop] lemma localFlux_integrand_continuous {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (α : ℝ) :
    Continuous (fun z : ℝ × ℝ => z.2 ^ 8 *
      localTrialExtension δ hδ fp.2 (z.2 ^ 2 * z.1) ^ α) := by
  have hp : Continuous (fun z : ℝ × ℝ =>
      localTrialExtension δ hδ fp.2 (z.2 ^ 2 * z.1) ^ α) :=
    (show Continuous (fun z : ℝ × ℝ =>
      localTrialExtension δ hδ fp.2 (z.2 ^ 2 * z.1)) by fun_prop).rpow_const
        (fun z => Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
          (localTrialExtension_mem hδ hfp _).2.1)))
  fun_prop

-- @node: localAverage_pos
/-- If [δ is positive](hyp:hδ) and [both trial components stay within one half
of one](hyp:hfp), [for every real α and s, the integral from zero to one of
v to the eighth power times the extended first component at v²s times the
extended second component at v²s raised to α is strictly positive](goal). -/
lemma localAverage_pos {δ : ℝ} (hδ : 0 < δ) {fp : LocalTrialPair δ}
    (hfp : fp ∈ localTrialSet δ) (α s : ℝ) :
    0 < ∫ v : ℝ in 0..1, v ^ 8 * localTrialExtension δ hδ fp.1 (v ^ 2 * s) *
      localTrialExtension δ hδ fp.2 (v ^ 2 * s) ^ α := by
  have hpos (v : ℝ) : 0 < localTrialExtension δ hδ fp.1 (v ^ 2 * s) ∧
      0 < localTrialExtension δ hδ fp.2 (v ^ 2 * s) := by
    have h := localTrialExtension_mem hδ hfp (v ^ 2 * s)
    constructor <;> linarith [h.1.1, h.2.1]
  apply intervalIntegral.integral_pos (by norm_num)
  · exact ((localAverage_integrand_continuous hδ hfp α).comp
      (continuous_const.prodMk continuous_id)).continuousOn
  · intro v hv
    exact mul_nonneg (mul_nonneg (pow_nonneg hv.1.le _) (hpos v).1.le)
      (Real.rpow_pos_of_pos (hpos v).2 _).le
  · refine ⟨1, by norm_num, ?_⟩
    exact mul_pos (mul_pos (by norm_num) (hpos 1).1)
      (Real.rpow_pos_of_pos (hpos 1).2 _)

-- @node: localQ_pos
/-- If [δ is positive](hyp:hδ) and [both trial components stay within one half
of one](hyp:hfp), [the local slope average is strictly positive at every real
auxiliary coordinate s](goal). -/
lemma localQ_pos {δ : ℝ} (hδ : 0 < δ) {fp : LocalTrialPair δ}
    (hfp : fp ∈ localTrialSet δ) (s : ℝ) : 0 < localQ δ hδ fp hfp s := by
  exact Real.rpow_pos_of_pos (mul_pos (by norm_num)
    (localAverage_pos hδ hfp (-radialGamma) s)) _

-- @node: localJ_pos
/-- If [δ is positive](hyp:hδ) and [both trial components stay within one half
of one](hyp:hfp), [the local flux average is strictly positive at every real
auxiliary coordinate s](goal). -/
lemma localJ_pos {δ : ℝ} (hδ : 0 < δ) {fp : LocalTrialPair δ}
    (hfp : fp ∈ localTrialSet δ) (s : ℝ) : 0 < localJ δ hδ fp hfp s := by
  have hpos (v : ℝ) : 0 < localTrialExtension δ hδ fp.2 (v ^ 2 * s) := by
    linarith [(localTrialExtension_mem hδ hfp (v ^ 2 * s)).2.1]
  apply intervalIntegral.integral_pos (by norm_num)
  · exact ((localFlux_integrand_continuous hδ hfp (1 - radialGamma)).comp
      (continuous_const.prodMk continuous_id)).continuousOn
  · intro v hv
    exact mul_nonneg (pow_nonneg hv.1.le _) (Real.rpow_pos_of_pos (hpos v) _).le
  · refine ⟨1, by norm_num, ?_⟩
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (hpos 1) _)

-- @node: localAverage_continuous
/-- If [δ is positive](hyp:hδ) and [both trial components stay within one half
of one](hyp:hfp), [for every real exponent α, the integral from zero to one of
v to the eighth power times the extended first component at v²s times the
extended second component at v²s raised to α varies continuously with s on
the whole real line](goal). -/
@[fun_prop] lemma localAverage_continuous {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) (α : ℝ) :
    Continuous (fun s => ∫ v : ℝ in 0..1,
      v ^ 8 * localTrialExtension δ hδ fp.1 (v ^ 2 * s) *
        localTrialExtension δ hδ fp.2 (v ^ 2 * s) ^ α) := by
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun s v : ℝ => v ^ 8 * localTrialExtension δ hδ fp.1 (v ^ 2 * s) *
      localTrialExtension δ hδ fp.2 (v ^ 2 * s) ^ α)
    (localAverage_integrand_continuous hδ hfp α) (s := Icc (0 : ℝ) 1) isCompact_Icc
  simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc] using h

-- @node: localQ_continuous
/-- If [δ is positive](hyp:hδ) and [both trial components stay within one half
of one](hyp:hfp), [the local slope average is continuous on the whole real
auxiliary line](goal). -/
@[fun_prop] lemma localQ_continuous {δ : ℝ} (hδ : 0 < δ) {fp : LocalTrialPair δ}
    (hfp : fp ∈ localTrialSet δ) : Continuous (localQ δ hδ fp hfp) := by
  unfold localQ
  exact (continuous_const.mul (localAverage_continuous hδ hfp (-radialGamma))).rpow_const
    (fun _ => Or.inr (by norm_num))

-- @node: localJ_continuous
/-- If [δ is positive](hyp:hδ) and [both trial components stay within one half
of one](hyp:hfp), [the local flux average is continuous on the whole real
auxiliary line](goal). -/
@[fun_prop] lemma localJ_continuous {δ : ℝ} (hδ : 0 < δ) {fp : LocalTrialPair δ}
    (hfp : fp ∈ localTrialSet δ) : Continuous (localJ δ hδ fp hfp) := by
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun s v : ℝ => v ^ 8 *
      localTrialExtension δ hδ fp.2 (v ^ 2 * s) ^ (1 - radialGamma))
    (localFlux_integrand_continuous hδ hfp (1 - radialGamma))
    (s := Icc (0 : ℝ) 1) isCompact_Icc
  unfold localJ
  simpa only [intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc] using h

-- @node: localTransformValues_continuous
/-- If [δ is positive](hyp:hδ) and [both trial components stay within one half
of one](hyp:hfp), [the pair of local integral transform values varies
continuously over the closed interval from −δ to δ](goal). -/
@[fun_prop] lemma localTransformValues_continuous {δ : ℝ} (hδ : 0 < δ)
    {fp : LocalTrialPair δ} (hfp : fp ∈ localTrialSet δ) :
    Continuous (localTransformValues δ hδ fp hfp) := by
  have hq := localQ_continuous hδ hfp
  have hj := localJ_continuous hδ hfp
  have hflux : Continuous (fun a => localJ δ hδ fp hfp a *
      localQ δ hδ fp hfp a ^ (1 - (radialDim : ℝ))) := by
    exact hj.mul (hq.rpow_const (fun a => Or.inl (localQ_pos hδ hfp a).ne'))
  have hf := (intervalIntegral.differentiable_integral_of_continuous hq
    (a := 0)).continuous
  have hp := (intervalIntegral.differentiable_integral_of_continuous hflux
    (a := 0)).continuous
  unfold localTransformValues
  fun_prop

-- @node: exists_smallLocalRadius
/-- [For any real displacement coefficient M and Lipschitz coefficient L,
there exists a positive interval half-width δ such that M times δ is at most
one half and L times δ is strictly less than one](goal). -/
lemma exists_smallLocalRadius (M L : ℝ) : ∃ δ, SmallLocalRadius M L δ := by
  let D := 4 * (|M| + |L| + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hcancel : D * D⁻¹ = 1 := mul_inv_cancel₀ hD.ne'
  refine ⟨D⁻¹, inv_pos.mpr hD, ?_, ?_⟩
  · have hM : M ≤ D / 2 := by dsimp [D]; linarith [le_abs_self M, abs_nonneg L]
    calc
      M * D⁻¹ ≤ (D / 2) * D⁻¹ := mul_le_mul_of_nonneg_right hM (inv_nonneg.mpr hD.le)
      _ = 1 / 2 := by nlinarith
  · have hL : L < D := by dsimp [D]; linarith [le_abs_self L, abs_nonneg M, abs_nonneg L]
    calc
      L * D⁻¹ < D * D⁻¹ := mul_lt_mul_of_pos_right hL (inv_pos.mpr hD)
      _ = 1 := hcancel

/-- For [a positive interval half-width δ](hyp:hδ) and [a continuous trial pair
whose components stay within one half of one](hyp:fp), [the continuous local
transform](goal) is the pair of continuous functions on the interval from −δ
to δ obtained by taking the two components of the local integral transform
values. -/
-- @node: localTransform
def localTransform {δ : ℝ} (hδ : 0 < δ) (fp : ↥(localTrialSet δ)) : LocalTrialPair δ :=
  (⟨fun s => (localTransformValues δ hδ fp.1 fp.2 s).1,
    (localTransformValues_continuous hδ fp.2).fst⟩,
   ⟨fun s => (localTransformValues δ hδ fp.1 fp.2 s).2,
    (localTransformValues_continuous hδ fp.2).snd⟩)

-- @node: localTransform_mem
/-- If [the local integral transform satisfies the uniform displacement and
Lipschitz bounds with coefficients M and L](hyp:hBounds) and [δ is positive,
M times δ is at most one half, and L times δ is less than one](hyp:hδ),
[transforming any trial pair whose components stay within one half of one
produces another pair with the same bounds](goal). -/
lemma localTransform_mem {M L δ : ℝ} (hBounds : LocalContractionBounds M L)
    (hδ : SmallLocalRadius M L δ) (fp : ↥(localTrialSet δ)) :
    localTransform hδ.1 fp ∈ localTrialSet δ := by
  have hb := (hBounds δ hδ.1 fp.1 fp.2).1
  constructor
  · intro s
    exact (le_max_left _ _).trans ((hb s).trans hδ.2.1)
  · intro s
    exact (le_max_right _ _).trans ((hb s).trans hδ.2.1)

-- @node: localTransform_dist_le
/-- If [the local integral transform satisfies the uniform displacement and
Lipschitz bounds with coefficients M and L](hyp:hBounds) and [δ is positive](hyp:hδ),
[the distance between the transforms of any two admissible trial pairs is at
most the larger of zero and L times δ, multiplied by the distance between
the original pairs](goal). -/
lemma localTransform_dist_le {M L δ : ℝ} (hBounds : LocalContractionBounds M L)
    (hδ : 0 < δ) (fp gp : ↥(localTrialSet δ)) :
    dist (localTransform hδ fp) (localTransform hδ gp) ≤
      max 0 (L * δ) * dist fp gp := by
  have hb := (hBounds δ hδ fp.1 fp.2).2 gp.1 gp.2
  have hnonneg : 0 ≤ max 0 (L * δ) * dist fp gp :=
    mul_nonneg (le_max_left _ _) dist_nonneg
  change max (dist (localTransform hδ fp).1 (localTransform hδ gp).1)
    (dist (localTransform hδ fp).2 (localTransform hδ gp).2) ≤ _
  apply max_le
  · apply (ContinuousMap.dist_le hnonneg).mpr
    intro s
    rw [Real.dist_eq]
    exact ((le_max_left _ _).trans (hb s)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)
  · apply (ContinuousMap.dist_le hnonneg).mpr
    intro s
    rw [Real.dist_eq]
    exact ((le_max_right _ _).trans (hb s)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)

/-- If [the local integral transform satisfies uniform displacement and
Lipschitz bounds with coefficients M and L](hyp:hBounds), [there exist a
positive interval half-width δ and a continuous trial pair whose components
stay within one half of one, such that M times δ is at most one half,
L times δ is less than one, and the pair equals its local integral transform
at every point of the interval](goal).

This is the Banach fixed-point step, conditional on the uniform estimates. -/
-- @node: exists_local_integral_fixedPoint
lemma exists_local_integral_fixedPoint {M L : ℝ} (hBounds : LocalContractionBounds M L) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (fp : LocalTrialPair δ) (hfp : fp ∈ localTrialSet δ),
      SmallLocalRadius M L δ ∧
      ∀ s, (fp.1 s, fp.2 s) = localTransformValues δ hδ fp hfp s := by
  obtain ⟨δ, hδ⟩ := exists_smallLocalRadius M L
  let : CompleteSpace ↥(localTrialSet δ) := (localTrialSet_isClosed δ).isComplete.completeSpace_coe
  let : Nonempty ↥(localTrialSet δ) := (localTrialSet_nonempty δ).to_subtype
  let T : ↥(localTrialSet δ) → ↥(localTrialSet δ) :=
    fun fp => ⟨localTransform hδ.1 fp, localTransform_mem hBounds hδ fp⟩
  let K : ℝ≥0 := ⟨max 0 (L * δ), le_max_left _ _⟩
  have hT : ContractingWith K T := by
    constructor
    · change max 0 (L * δ) < 1
      exact max_lt (by norm_num) hδ.2.2
    · apply lipschitzWith_iff_dist_le_mul.mpr
      intro fp gp
      exact localTransform_dist_le hBounds hδ.1 fp gp
  let fp := hT.fixedPoint T
  have hfix : T fp = fp := hT.fixedPoint_isFixedPt
  refine ⟨δ, hδ.1, fp.1, fp.2, hδ, ?_⟩
  intro s
  have hval : localTransform hδ.1 fp = fp.1 := congrArg Subtype.val hfix
  exact (congrArg (fun gp : LocalTrialPair δ => (gp.1 s, gp.2 s)) hval).symm

end OaiSmoothNonquadraticAffine
