module
public import Papers.TsAdaptiveEstimationInference.Helpers.SpectralMoments
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
/-! Commutation bridges for the real functional calculus. -/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
open Causalean.Estimation.NPIV.Complexification
open scoped InnerProductSpace
attribute [local instance 2000] instAlgebraRealLpCLM
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
-- @node: realCFC_commute
/-- If [A is self-adjoint](hyp:hA), [A commutes with B](hyp:hAB), and
[f is continuous](hyp:hf), then [applying f to A by the real continuous
functional calculus produces an operator that commutes with B](goal). -/
lemma realCFC_commute (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hA : IsSelfAdjoint A) (hAB : Commute A B) (f : ℝ → ℝ) (hf : Continuous f) :
    Commute (realCFC A f) B := by
  have hlift : Commute (complexLift A) (complexLift B) := by
    apply ContinuousLinearMap.ext
    intro u
    have h := congrArg (fun T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => T (reLp u)) hAB.eq
    have h' := congrArg (fun T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => T (imLp u)) hAB.eq
    simp only [ContinuousLinearMap.mul_apply] at h h'
    simp only [ContinuousLinearMap.mul_apply]
    rw [complexLift_apply A, complexLift_apply B (complexLift A u),
      reLp_complexLift, imLp_complexLift, reLp_complexLift, imLp_complexLift, h, h']
  have hc := (complexLift_isSelfAdjoint hA).commute_cfc hlift
    (fun z : ℂ => (f z.re : ℂ))
  apply ContinuousLinearMap.ext
  intro u
  have he := congrArg (fun T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ => reLp (T (ιLp u))) hc.eq
  simp only [ContinuousLinearMap.mul_apply, complexLift_real, reLp_complexLift] at he
  simpa only [ContinuousLinearMap.mul_apply, realCFC_apply A hA f hf] using he
-- @node: paper_complexLift_one
/-- [Complexifying the identity operator on the real square-integrable functions
gives the identity operator on the complex square-integrable functions](goal). -/
lemma paper_complexLift_one :
    complexLift (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))
      = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  ext1 f
  simpa [complexLift_apply] using reLp_add_smul_imLp (μ := μ) f

-- @node: paper_complexLift_comp
/-- [Complexifying the composition of two bounded real linear operators gives
the composition of their complexifications, in the same order](goal). -/
lemma paper_complexLift_comp (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A.comp B) = (complexLift A).comp (complexLift B) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply]
  rw [complexLift_apply, complexLift_apply]
  rw [reLp_complexLift, imLp_complexLift]
  rfl

-- @node: paper_complexLift_mul
/-- [Complexification preserves the product of two bounded real linear
operators on square-integrable functions](goal). -/
lemma paper_complexLift_mul (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A * B) = complexLift A * complexLift B := by
  exact paper_complexLift_comp A B

-- @node: paper_complexLift_sub
/-- [Complexifying the difference of two bounded real linear operators gives
the difference of their complexifications](goal). -/
lemma paper_complexLift_sub (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A - B) = complexLift A - complexLift B := by
  ext1 f
  rw [complexLift_apply]
  change ιLp (A (reLp f) - B (reLp f)) + Complex.I • ιLp (A (imLp f) - B (imLp f)) =
    complexLift A f - complexLift B f
  rw [complexLift_apply A f, complexLift_apply B f]
  rw [map_sub, map_sub, smul_sub]
  abel

-- @node: paper_complexLift_algebraMap_real
/-- [Complexifying multiplication by a real scalar gives multiplication by
the same scalar on the complex square-integrable functions](goal). -/
lemma paper_complexLift_algebraMap_real (r : ℝ) :
    complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r)
      = algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) := by
  ext1 f
  rw [complexLift_apply]
  change ιLp (r • reLp f) + Complex.I • ιLp (r • imLp f) = (r : ℂ) • f
  calc
    ιLp (r • reLp f) + Complex.I • ιLp (r • imLp f)
        = (r : ℂ) • (ιLp (reLp f) + Complex.I • ιLp (imLp f)) := by
      rw [smul_add]
      simp only [map_smul]
      congr 1
      change Complex.I • ((r : ℂ) • ιLp (imLp f)) =
        (r : ℂ) • (Complex.I • ιLp (imLp f))
      rw [smul_smul, smul_smul, mul_comm]
    _ = (r : ℂ) • f := by rw [reLp_add_smul_imLp]

-- @node: paper_complexLift_resolvent_real
/-- [The difference between a real scalar times the complex identity and the
complexification of A is the complexification of that scalar times the real
identity minus A](goal). -/
lemma paper_complexLift_resolvent_real
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (r : ℝ) :
    algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) - complexLift A =
      complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r - A) := by
  rw [paper_complexLift_sub, paper_complexLift_algebraMap_real]

-- @node: paper_complexLift_isUnit
/-- If [a bounded real linear operator B is invertible](hyp:hB), then
[its complexification is invertible](goal). -/
lemma paper_complexLift_isUnit
    {B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hB : IsUnit B) :
    IsUnit (complexLift B) := by
  have hone : complexLift (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) =
      (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
    exact paper_complexLift_one (μ := μ)
  refine Units.isUnit ⟨complexLift B, complexLift ↑hB.unit⁻¹, ?_, ?_⟩
  · calc
      complexLift B * complexLift ↑hB.unit⁻¹ = complexLift (B * ↑hB.unit⁻¹) := by
        rw [paper_complexLift_mul]
      _ = complexLift 1 := congrArg (fun T => complexLift T) hB.mul_val_inv
      _ = 1 := hone
  · calc
      complexLift ↑hB.unit⁻¹ * complexLift B = complexLift (↑hB.unit⁻¹ * B) := by
        rw [paper_complexLift_mul]
      _ = complexLift 1 := congrArg (fun T => complexLift T) hB.val_inv_mul
      _ = 1 := hone

-- @node: paper_spectrum_complexLift_subset_real
/-- If [A is self-adjoint](hyp:hA) and [z belongs to the complex spectrum of
its complexification](hyp:hz), then [the real part of z belongs to the real
spectrum of A](goal). -/
theorem paper_spectrum_complexLift_subset_real
    {A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ spectrum ℂ (complexLift A)) :
    z.re ∈ spectrum ℝ A := by
  by_contra hzreal
  have hunitR : IsUnit (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) z.re - A) :=
    spectrum.notMem_iff.mp hzreal
  have hunitC :
      IsUnit (algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (z.re : ℂ) - complexLift A) := by
    rw [paper_complexLift_resolvent_real]
    exact paper_complexLift_isUnit hunitR
  have hzreal_eq : z = (z.re : ℂ) :=
    IsSelfAdjoint.mem_spectrum_eq_re (complexLift_isSelfAdjoint hA) hz
  have hnot : (z.re : ℂ) ∉ spectrum ℂ (complexLift A) :=
    spectrum.notMem_iff.mpr hunitC
  exact hnot (by rwa [← hzreal_eq])

-- @node: realCFC_congr_spectrum
/-- If [A is self-adjoint](hyp:hA) and [f and g agree at every point of its real
spectrum](hyp:hfg), then [f and g give the same operator under the real
continuous functional calculus at A](goal). -/
lemma realCFC_congr_spectrum (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hA : IsSelfAdjoint A) (f g : ℝ → ℝ)
    (hfg : ∀ x ∈ spectrum ℝ A, f x = g x) : realCFC A f = realCFC A g := by
  apply ContinuousLinearMap.ext
  intro u
  change reLp (cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) (ιLp u)) =
    reLp (cfc (fun z : ℂ => (g z.re : ℂ)) (complexLift A) (ιLp u))
  congr 2
  apply cfc_congr
  intro z hz
  exact congrArg Complex.ofReal (hfg z.re (paper_spectrum_complexLift_subset_real hA hz))

end Papers.TsAdaptiveEstimationInference
