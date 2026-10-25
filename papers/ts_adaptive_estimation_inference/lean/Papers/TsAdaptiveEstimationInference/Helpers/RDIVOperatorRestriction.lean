module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVDensityReduction
/-! A common sigma-finite restriction for all RDIV operator integrals.

The exceptional input set is fixed by the true density, before any fitted
hypothesis or density is selected. The same restriction works at the actual
calibration inputs. No measurability of evaluation of a random L2 selection is
asserted here.
-/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory

variable {X Z W Ω : Type*} [MeasurableSpace X] [MeasurableSpace Z]
  [MeasurableSpace W] [MeasurableSpace Ω]

/-- If [the restriction set is measurable](hyp:hs), [the signed test is almost
everywhere strongly measurable](hyp:hf), [the dominating density is integrable](hyp:hg),
[the test's absolute value is bounded by a constant times that density](hyp:hdom),
and [the density vanishes almost everywhere outside the restriction set](hyp:hz),
[the test is integrable and restricting its integral to that set leaves the
integral unchanged](goal). -/
-- @node: rdiv_signed_integral_restrict_of_density_domination
lemma rdiv_signed_integral_restrict_of_density_domination
    (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (f g : X → ℝ) (C : ℝ) (hf : AEStronglyMeasurable f μ)
    (hg : Integrable g μ) (hdom : ∀ x, |f x| ≤ C * g x)
    (hz : g =ᵐ[μ.restrict sᶜ] 0) :
    Integrable f μ ∧ (∫ x in s, f x ∂μ) = ∫ x, f x ∂μ := by
  have hi : Integrable f μ := (hg.const_mul C).mono' hf
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hdom x)
  have hfz : f =ᵐ[μ.restrict sᶜ] 0 := by
    filter_upwards [hz] with x hx
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    simpa only [hx, Pi.zero_apply, mul_zero] using hdom x
  have hzero : ∫ x in sᶜ, f x ∂μ = 0 := by
    simpa using integral_congr_ae hfz
  exact ⟨hi, by simpa only [hzero, add_zero] using integral_add_compl hs hi⟩

/-- Suppose [the restriction set is measurable](hyp:hs), [the density class is
realizable](hyp:hDensity), [common-support density bounds hold](hyp:hBounds),
[hypotheses have envelope B on that support](hyp:hHyp), and [B is nonnegative](hyp:hB).
At an instrument value where [the true density section is integrable](hyp:hi)
and [vanishes almost everywhere outside the restriction set](hyp:hz), [every
class density and hypothesis give an integrable signed operator test, and
restricting its reference measure leaves the operator value unchanged](goal). -/
-- @node: rdiv_density_operator_integral_restrict
lemma rdiv_density_operator_integral_restrict
    (V : IVWorld W X Z) (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (z : Z) (hi : Integrable (fun x => g₀ x z) μ)
    (hz : (fun x => g₀ x z) =ᵐ[μ.restrict sᶜ] 0) :
    ∀ g ∈ G, ∀ h ∈ V.H,
      Integrable (fun x => primalVersion V h x * g x z) μ ∧
        densityOperator (μ.restrict s) g (primalVersion V h) z =
          densityOperator μ g (primalVersion V h) z := by
  intro g hg h hh
  apply rdiv_signed_integral_restrict_of_density_domination μ s hs
    (fun x => primalVersion V h x * g x z) (fun x => g₀ x z) (B * (CG / c₀))
    ((V.primal_measurable h).mul
      (hDensity.2 g hg).1.of_uncurry_right).aestronglyMeasurable hi _ hz
  intro x
  by_cases hx : (x, z) ∈ support
  · rw [abs_mul, abs_of_nonneg ((hDensity.2 g hg).2.1 x z)]
    calc
      |primalVersion V h x| * g x z ≤ B * g x z :=
        mul_le_mul_of_nonneg_right (hHyp h hh (x, z) hx)
          ((hDensity.2 g hg).2.1 x z)
      _ ≤ B * ((CG / c₀) * g₀ x z) :=
        mul_le_mul_of_nonneg_left
          (rdiv_density_ratio_of_bounds G g₀ g support c₀ CG hBounds
            hDensity.1 hg x z) hB
      _ = _ := by ring
  · rw [hBounds.2.2.2.2 g hg (x, z) hx, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hB (div_nonneg hBounds.2.1.le hBounds.1.le))
      ((hDensity.2 g₀ hDensity.1).2.1 x z)

/-- Under [the conditional-density IV setting](hyp:hIV), [density-class
realizability](hyp:hDensity), [common-support density bounds](hyp:hBounds), and
[a hypothesis envelope of size B](hyp:hHyp) with [B nonnegative](hyp:hB), [there
exists a measurable input set on which the reference measure is sigma-finite
and which preserves integrability and every class operator integral, both at
almost every fresh instrument value and almost surely at every calibration
observation for every sample size](goal). -/
-- @node: rdiv_density_operator_common_restriction
lemma rdiv_density_operator_common_restriction
    (V : IVWorld W X Z) (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B) :
    ∃ s : Set X, MeasurableSet s ∧ SigmaFinite (μ.restrict s) ∧
      (∀ᵐ z ∂V.law.map V.zOf, ∀ g ∈ G, ∀ h ∈ V.H,
        Integrable (fun x => primalVersion V h x * g x z) μ ∧
        densityOperator (μ.restrict s) g (primalVersion V h) z =
          densityOperator μ g (primalVersion V h) z) ∧
      ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ i ∈ split.cal n, ∀ g ∈ G, ∀ h ∈ V.H,
        Integrable (fun x => primalVersion V h x * g x (V.zOf (sample.Z i ω))) μ ∧
        densityOperator (μ.restrict s) g (primalVersion V h)
            (V.zOf (sample.Z i ω)) =
          densityOperator μ g (primalVersion V h) (V.zOf (sample.Z i ω)) := by
  obtain ⟨s, hs, hsf, hz⟩ := rdiv_true_density_sigmaFinite_restriction V μ G g₀
    hIV hDensity
  have hsections := hz.mono fun z hz => rdiv_density_operator_integral_restrict
    V μ s hs G g₀ support B c₀ CG hDensity hBounds hHyp hB z hz.1 hz.2
  refine ⟨s, hs, hsf, hsections, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ i : ℕ,
      Integrable (fun x => g₀ x (V.zOf (sample.Z i ω))) μ ∧
      (fun x => g₀ x (V.zOf (sample.Z i ω))) =ᵐ[μ.restrict sᶜ] 0 := by
    apply ae_all_iff.mpr
    intro i
    have hlaw : P.map (sample.Z i) = V.law := by
      rw [← (sample.identDist i).map_eq, sample.law]
    have hw := ae_of_ae_map V.measurable_z.aemeasurable hz
    rw [← hlaw] at hw
    exact ae_of_ae_map (sample.meas i).aemeasurable hw
  filter_upwards [hall] with ω hω
  intro n i _
  exact rdiv_density_operator_integral_restrict V μ s hs G g₀ support B c₀ CG
    hDensity hBounds hHyp hB _ (hω i).1 (hω i).2

/-- Under [the conditional-density IV setting](hyp:hIV), [density-class
realizability](hyp:hDensity), [common-support density bounds](hyp:hBounds), and
[a hypothesis envelope of size B](hyp:hHyp) with [B nonnegative](hyp:hB), assume
[the density estimator selects measurable likelihood maximizers](hyp:hMLE)
and [has a coherent selected-density version](hyp:hVersion). For [a positive
sample size](hyp:hn) and [a fixed primal element](hyp:h) [in the hypothesis
class](hyp:hh), [there exists an operator version jointly measurable in the
preliminary data and instrument, agreeing almost surely with the fitted
operator for almost every fresh instrument and at every calibration
observation](goal). -/
-- @node: rdiv_fixed_operator_calibration_version
lemma rdiv_fixed_operator_calibration_version
    (V : IVWorld W X Z) (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z)) (B c₀ CG : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hVersion : RDIVSelectedDensityVersion V P sample split μ gHat)
    (n : ℕ) (hn : 0 < n) (h : V.Hbar.toSubmodule) (hh : h ∈ V.H) :
    ∃ op : Ω × Z → ℝ,
      @Measurable (Ω × Z) ℝ
        ((preliminarySigma V P sample split n).prod inferInstance) inferInstance op ∧
      (∀ᵐ ω ∂P, (fun z => op (ω, z)) =ᵐ[V.law.map V.zOf]
        estimatedOperator V μ gHat n ω h) ∧
      ∀ᵐ ω ∂P, ∀ i ∈ split.cal n,
        op (ω, V.zOf (sample.Z i ω)) =
          estimatedOperator V μ gHat n ω h (V.zOf (sample.Z i ω)) := by
  obtain ⟨s, hs, hsf, hfresh, hcal⟩ := rdiv_density_operator_common_restriction
    V P sample split μ G g₀ support B c₀ CG hIV hDensity hBounds hHyp hB
  let : SigmaFinite (μ.restrict s) := hsf
  obtain ⟨gBar, hgBar, _, hsections, hactual⟩ := hVersion n hn
  let op : Ω × Z → ℝ := fun p =>
    ∫ x in s, primalVersion V h x * gBar (p.1, (x, p.2)) ∂μ
  refine ⟨op, ?_, ?_, ?_⟩
  · let : MeasurableSpace Ω := preliminarySigma V P sample split n
    have hm : Measurable (fun p : (Ω × Z) × X =>
        primalVersion V h p.2 * gBar (p.1.1, (p.2, p.1.2))) := by
      have hp : Measurable (primalVersion V h) := V.primal_measurable h
      exact (hp.comp measurable_snd).mul
        (hgBar.comp (measurable_fst.fst.prodMk
          (measurable_snd.prodMk measurable_fst.snd)))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  · filter_upwards [(hMLE n hn).1, hsections] with ω hg heq
    filter_upwards [hfresh, heq] with z hz hx
    change (∫ x in s, primalVersion V h x * gBar (ω, (x, z)) ∂μ) =
      densityOperator μ (gHat n ω) (primalVersion V h) z
    calc
      _ = densityOperator (μ.restrict s) (gHat n ω) (primalVersion V h) z := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hx] with x hxeq
        rw [hxeq]
      _ = _ := (hz _ hg.1 h hh).2
  · filter_upwards [(hMLE n hn).1, hactual, hcal] with ω hg heq hrestrict
    intro i hi
    change (∫ x in s, primalVersion V h x * gBar (ω, (x, V.zOf (sample.Z i ω))) ∂μ) =
      densityOperator μ (gHat n ω) (primalVersion V h) (V.zOf (sample.Z i ω))
    calc
      _ = densityOperator (μ.restrict s) (gHat n ω) (primalVersion V h)
          (V.zOf (sample.Z i ω)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (heq i hi)] with x hxeq
        rw [hxeq]
      _ = _ := (hrestrict n i hi _ hg.1 h hh).2

end Papers.TsAdaptiveEstimationInference
