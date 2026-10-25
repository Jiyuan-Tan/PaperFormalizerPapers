module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVLossBridge
/-! Conditional Jensen and the density-ratio reduction of fitting coordinates. -/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-- If [g is integrable](hyp:hg), [nonnegative everywhere](hyp:hg0), and [has
integral one](hyp:hgn), [u is strongly measurable up to a null set](hyp:hu), and
[u² times g is integrable](hyp:hmoment), then [the square of the integral of u
times g is at most the integral of u² times g](goal). -/
-- @node: rdiv_density_operator_jensen_sq
lemma rdiv_density_operator_jensen_sq (μ : Measure X) (g u : X → ℝ)
    (hg : Integrable g μ) (hg0 : ∀ x, 0 ≤ g x) (hgn : ∫ x, g x ∂μ = 1)
    (hu : AEStronglyMeasurable u μ)
    (hmoment : Integrable (fun x => u x ^ 2 * g x) μ) :
    (∫ x, u x * g x ∂μ) ^ 2 ≤ ∫ x, u x ^ 2 * g x ∂μ := by
  let v := fun x => u x * Real.sqrt (g x)
  let w := fun x => Real.sqrt (g x)
  have hvm : AEStronglyMeasurable v μ := by fun_prop
  have hvSq : Integrable (fun x => v x ^ 2) μ := by
    simpa only [v, mul_pow, Real.sq_sqrt (hg0 _)] using hmoment
  have hv : MemLp v 2 μ := (memLp_two_iff_integrable_sq hvm).2 hvSq
  have hw : MemLp w 2 μ := Causalean.Stat.Minimax.sqrt_density_memLp μ g hg hg0
  have hfact : (fun x => u x * g x) = fun x => v x * w x := by
    funext x
    dsimp [v, w]
    rw [mul_assoc, ← pow_two, Real.sq_sqrt (hg0 x)]
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x => abs_nonneg (v x))
    (Filter.Eventually.of_forall fun x => abs_nonneg (w x))
    (by norm_num; exact hv.abs) (by norm_num; exact hw.abs)
  simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] at hholder
  have hmean : |∫ x, v x * w x ∂μ| ≤
      Real.sqrt (∫ x, v x ^ 2 ∂μ) * Real.sqrt (∫ x, w x ^ 2 ∂μ) := by
    exact abs_integral_le_integral_abs.trans (by simpa only [abs_mul] using hholder)
  have hs := pow_le_pow_left₀ (abs_nonneg _) hmean 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (v x)),
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (w x))] at hs
  rw [hfact]
  simpa only [v, w, mul_pow, Real.sq_sqrt (hg0 _), hgn, mul_one] using hs

variable {𝒲 Z : Type*} [MeasurableSpace 𝒲] [MeasurableSpace Z]
  (V : IVWorld 𝒲 X Z)

/-- Suppose [the instrument space is the full instrument-measurable L² space, the
true density generates the joint input–instrument law, and the moment representer
gives the conditional outcome mean](hyp:hIV), [the density class contains
the true density and consists of measurable, nonnegative conditional densities
normalized almost everywhere](hyp:hDensity), [the true density is bounded below
by positive c₀ on the common support and class densities are bounded above by
positive CG there and vanish outside it](hyp:hBounds), and [g belongs to this
class](hyp:hg). If [u is measurable](hyp:hu) and [square-integrable under the input
distribution](hyp:hu2), then [the instrument-law L² norm of its density-operator
image under g is at most √(CG/c₀) times its input-law L² norm](goal). -/
-- @node: rdiv_density_operator_input_bound
lemma rdiv_density_operator_input_bound (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ g : X → Z → ℝ)
    (support : Set (X × Z)) (c₀ CG : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG) (hg : g ∈ G)
    (u : X → ℝ) (hu : Measurable u) (hu2 : MemLp u 2 (V.law.map V.xOf)) :
    inputL2Norm (V.law.map V.zOf) (densityOperator μ g u) ≤
      Real.sqrt (CG / c₀) * inputL2Norm (V.law.map V.xOf) u := by
  let R := CG / c₀
  have hR : 0 ≤ R := div_nonneg hBounds.2.1.le hBounds.1.le
  have hratio := rdiv_density_ratio_of_bounds G g₀ g support c₀ CG
    hBounds hDensity.1 hg
  have hgm : Measurable (Function.uncurry g) := (hDensity.2 g hg).1
  have hout : AEStronglyMeasurable (densityOperator μ g u) (V.law.map V.zOf) := by
    apply rdiv_density_supported_integral_aestronglyMeasurable V μ G g₀ hIV hDensity
      (fun p => u p.1 * g p.1 p.2) ((hu.comp measurable_fst).mul hgm)
    intro x z hx
    have hz := hratio x z
    rw [hx, mul_zero] at hz
    have hgzero : g x z = 0 := le_antisymm hz ((hDensity.2 g hg).2.1 x z)
    simp only [hgzero, mul_zero]
  obtain ⟨hsec, hint, heq⟩ := rdiv_density_input_second_moment V μ G g₀
    hIV hDensity u hu hu2
  have hpoint : ∀ᵐ z ∂V.law.map V.zOf,
      densityOperator μ g u z ^ 2 ≤ R * ∫ x, u x ^ 2 * g₀ x z ∂μ := by
    filter_upwards [hsec, rdiv_density_integrable_of_realizable V μ G g₀ g hDensity hg,
      (hDensity.2 g hg).2.2] with z hmoment hgi hgn
    have hdom (x : X) : u x ^ 2 * g x z ≤ R * (u x ^ 2 * g₀ x z) := by
      have hb := mul_le_mul_of_nonneg_left (hratio x z) (sq_nonneg (u x))
      dsimp [R]
      nlinarith only [hb]
    have hfitmoment : Integrable (fun x => u x ^ 2 * g x z) μ := by
      apply (hmoment.const_mul R).mono' ((hu.pow_const 2).mul (hgm.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
      filter_upwards [] with x
      change |u x ^ 2 * g x z| ≤ _
      simpa only [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (sq_nonneg (u x)) ((hDensity.2 g hg).2.1 x z))] using hdom x
    have hj := rdiv_density_operator_jensen_sq μ (fun x => g x z) u hgi
      (fun x => (hDensity.2 g hg).2.1 x z) hgn hu.aestronglyMeasurable hfitmoment
    apply hj.trans
    rw [← integral_const_mul]
    exact integral_mono_ae hfitmoment (hmoment.const_mul R) (ae_of_all _ hdom)
  have houtSq : Integrable (fun z => densityOperator μ g u z ^ 2) (V.law.map V.zOf) := by
    apply (hint.const_mul R).mono' (hout.pow 2)
    filter_upwards [hpoint] with z hz
    change |densityOperator μ g u z ^ 2| ≤ _
    rwa [abs_of_nonneg (sq_nonneg _)]
  have henergy : (∫ z, densityOperator μ g u z ^ 2 ∂V.law.map V.zOf) ≤
      R * ∫ x, u x ^ 2 ∂V.law.map V.xOf := by
    rw [← heq, ← integral_const_mul]
    exact integral_mono_ae houtSq (hint.const_mul R) hpoint
  unfold inputL2Norm
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt hR, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (u x))]
  exact henergy

/-- Suppose [the instrument space is the full instrument-measurable L² space, the
true density generates the joint input–instrument law, and the moment representer
gives the conditional outcome mean](hyp:hIV), [the density class contains
the true density and consists of measurable, nonnegative conditional densities
normalized almost everywhere](hyp:hDensity), [the true density is bounded below
by positive c₀ on the common support and class densities are bounded above by
positive CG there and vanish outside it](hyp:hBounds), and [g belongs to this
class](hyp:hg). For [two elements h and h′ of the hypothesis Hilbert space](hyp:h,h'),
[the instrument-law L² norm of the density operator applied to the difference of
their chosen function representatives is at most √(CG/c₀) times their Hilbert
distance](goal). -/
-- @node: rdiv_fitting_coordinate_bound
lemma rdiv_fitting_coordinate_bound (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ g : X → Z → ℝ)
    (support : Set (X × Z)) (c₀ CG : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG) (hg : g ∈ G)
    (h h' : V.Hbar.toSubmodule) :
    inputL2Norm (V.law.map V.zOf)
      (densityOperator μ g (primalVersion V h - primalVersion V h')) ≤
      Real.sqrt (CG / c₀) * ‖h - h'‖ := by
  have hb := rdiv_density_operator_input_bound V μ G g₀ g support c₀ CG
    hIV hDensity hBounds hg (primalVersion V h - primalVersion V h')
    ((V.primal_measurable h).sub (V.primal_measurable h'))
    ((rdiv_primal_input_memLp_norm V h).1.sub (rdiv_primal_input_memLp_norm V h').1)
  rwa [rdiv_primal_difference_input_norm V h h'] at hb

/-- Suppose [the instrument space is the full instrument-measurable L² space, the
true density generates the joint input–instrument law, and the moment representer
gives the conditional outcome mean](hyp:hIV), [the density class contains
the true density and consists of measurable, nonnegative conditional densities
normalized almost everywhere](hyp:hDensity), [the true density is bounded below
by positive c₀ on the common support and class densities are bounded above by
positive CG there and vanish outside it](hyp:hBounds), [g belongs to this class](hyp:hg),
[C is nonnegative](hyp:hC), and [r is nonnegative](hyp:hr). For [hypothesis-space
elements h and h′](hyp:h,h'), if [the absolute deviation d is bounded by C times
the sum of r times their operator-image distance, r times their Hilbert distance,
and r²](hyp:hd), then [it is bounded by C times (√(CG/c₀) + 1) times the sum of
r times their Hilbert distance and r²](goal). -/
-- @node: rdiv_fitting_deviation_reduction
lemma rdiv_fitting_deviation_reduction (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ g : X → Z → ℝ)
    (support : Set (X × Z)) (c₀ CG C r d : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG) (hg : g ∈ G)
    (hC : 0 ≤ C) (hr : 0 ≤ r) (h h' : V.Hbar.toSubmodule)
    (hd : |d| ≤ C * (r * inputL2Norm (V.law.map V.zOf)
      (densityOperator μ g (primalVersion V h - primalVersion V h')) +
        r * ‖h - h'‖ + r ^ 2)) :
    |d| ≤ (C * (Real.sqrt (CG / c₀) + 1)) * (r * ‖h - h'‖ + r ^ 2) := by
  have hb := rdiv_fitting_coordinate_bound V μ G g₀ g support c₀ CG
    hIV hDensity hBounds hg h h'
  calc
    _ ≤ C * (r * (Real.sqrt (CG / c₀) * ‖h - h'‖) + r * ‖h - h'‖ + r ^ 2) := by
      apply hd.trans
      gcongr
    _ ≤ _ := by
      nlinarith only [mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg (CG / c₀))) (sq_nonneg r)]

end Papers.TsAdaptiveEstimationInference
