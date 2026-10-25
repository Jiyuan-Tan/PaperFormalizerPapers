module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVCalibrationEvent
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVPerturbation
/-! A common sigma-finite restriction derived from the true joint density.
The dominating measure itself need not be sigma-finite. -/
public section
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped ENNReal

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

/-- If [g is jointly measurable](hyp:hg) and [nonnegative everywhere](hyp:hg0),
[its total mass under the input measure times the instrument probability law is
one](hyp:hmass), and [its input integral is one for almost every instrument
value](hyp:hnorm), then [there is a measurable input set on which the restricted
measure is sigma-finite and outside which almost every density section vanishes
almost everywhere](goal). -/
-- @node: rdiv_density_sigmaFinite_restriction
lemma rdiv_density_sigmaFinite_restriction (μ : Measure X) (ν : Measure Z)
    [IsProbabilityMeasure ν] (g : X → Z → ℝ)
    (hg : Measurable (Function.uncurry g)) (hg0 : ∀ x z, 0 ≤ g x z)
    (hmass : ∫⁻ p, ENNReal.ofReal (g p.1 p.2) ∂μ.prod ν = 1)
    (hnorm : ∀ᵐ z ∂ν, ∫ x, g x z ∂μ = 1) :
    ∃ s : Set X, MeasurableSet s ∧ SigmaFinite (μ.restrict s) ∧
      ∀ᵐ z ∂ν, (fun x => g x z) =ᵐ[μ.restrict sᶜ] 0 := by
  let k : X → ℝ≥0∞ := fun x => ∫⁻ z, ENNReal.ofReal (g x z) ∂ν
  have hkm : Measurable k := hg.ennreal_ofReal.lintegral_prod_right
  have hk : ∫⁻ x, k x ∂μ = 1 := (lintegral_prod _ hg.ennreal_ofReal.aemeasurable).symm.trans hmass
  have hkfin := ae_lt_top hkm (hk ▸ ENNReal.one_ne_top)
  have hki := integrable_toReal_of_lintegral_ne_top hkm.aemeasurable
    (hk ▸ ENNReal.one_ne_top)
  let s := hki.aefinStronglyMeasurable.sigmaFiniteSet
  have hs : MeasurableSet s := hki.aefinStronglyMeasurable.measurableSet
  have : SigmaFinite (μ.restrict s) := hki.aefinStronglyMeasurable.sigmaFinite_restrict
  have hzero : k =ᵐ[μ.restrict sᶜ] 0 := by
    filter_upwards [hki.aefinStronglyMeasurable.ae_eq_zero_compl,
      ae_restrict_of_ae hkfin] with x hx hxf
    exact (ENNReal.toReal_eq_zero_iff _).1 hx |>.resolve_right hxf.ne
  have hks : ∫⁻ x in s, k x ∂μ = 1 := by
    have hz := lintegral_congr_ae hzero
    simpa [hz] using (lintegral_add_compl k hs).trans hk
  let q : Z → ℝ≥0∞ := fun z => ∫⁻ x in s, ENNReal.ofReal (g x z) ∂μ
  have hqm : Measurable q := hg.ennreal_ofReal.lintegral_prod_left
  have hq : ∫⁻ z, q z ∂ν = 1 := by
    rw [← lintegral_lintegral_swap hg.ennreal_ofReal.aemeasurable]
    exact hks
  have hqle : q ≤ᵐ[ν] fun _ => 1 := by
    filter_upwards [hnorm] with z hz
    have hi : Integrable (fun x => g x z) μ := by
      by_contra h
      rw [integral_undef h] at hz
      norm_num at hz
    have hfull : ∫⁻ x, ENNReal.ofReal (g x z) ∂μ = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x => hg0 x z)), hz]
      simp
    exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans hfull.le
  have hqone : q =ᵐ[ν] fun _ => 1 :=
    ae_eq_of_ae_le_of_lintegral_le hqle (hq ▸ ENNReal.one_ne_top)
      measurable_const.aemeasurable (by simp [hq])
  refine ⟨s, hs, inferInstance, ?_⟩
  filter_upwards [hnorm, hqone] with z hz hqz
  have hi : Integrable (fun x => g x z) μ := by
    by_contra h
    rw [integral_undef h] at hz
    norm_num at hz
  have hrestricted : ∫ x in s, g x z ∂μ = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => hg0 x z))
      (hg.of_uncurry_right.stronglyMeasurable.aestronglyMeasurable)]
    change (q z).toReal = 1
    rw [hqz]; simp
  apply (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun x => hg0 x z))
    hi.integrableOn).1
  linarith [integral_add_compl hs hi]

/-- If [s is measurable](hyp:hs), [f is strongly measurable up to a null set](hyp:hf)
and [nonnegative everywhere](hyp:hf0), [g is integrable](hyp:hg), [f is everywhere
at most C times g](hyp:hdom), and [g vanishes almost everywhere outside s](hyp:hz),
then [f is integrable and its integral over s equals its integral over the whole
input space](goal). -/
-- @node: rdiv_integral_restrict_of_density_domination
lemma rdiv_integral_restrict_of_density_domination (μ : Measure X)
    (s : Set X) (hs : MeasurableSet s) (f g : X → ℝ) (C : ℝ)
    (hf : AEStronglyMeasurable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hg : Integrable g μ) (hdom : ∀ x, f x ≤ C * g x)
    (hz : g =ᵐ[μ.restrict sᶜ] 0) :
    Integrable f μ ∧ (∫ x in s, f x ∂μ) = ∫ x, f x ∂μ := by
  have hi : Integrable f μ := (hg.const_mul C).mono' hf (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hdom x)
  have hfz : f =ᵐ[μ.restrict sᶜ] 0 := by
    filter_upwards [hz] with x hx
    exact le_antisymm (by simpa [hx] using hdom x) (hf0 x)
  refine ⟨hi, ?_⟩
  have hzero : ∫ x in sᶜ, f x ∂μ = 0 := by
    simpa using integral_congr_ae hfz
  simpa [hzero] using integral_add_compl hs hi

variable {𝒲 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace Ω]
  (V : IVWorld 𝒲 X Z) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- If [the instrument space is the full instrument-measurable L² space, the true
density generates the joint input–instrument law, and the moment representer
gives the conditional outcome mean](hyp:hIV) and [the density
class contains the true density and consists of measurable, nonnegative conditional
densities normalized almost everywhere](hyp:hDensity), then [there is a measurable
input set with sigma-finite restricted measure such that, for almost every
instrument value, the true density section is integrable and vanishes almost
everywhere outside that set](goal). -/
-- @node: rdiv_true_density_sigmaFinite_restriction
lemma rdiv_true_density_sigmaFinite_restriction (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀) :
    ∃ s : Set X, MeasurableSet s ∧ SigmaFinite (μ.restrict s) ∧
      ∀ᵐ z ∂V.law.map V.zOf, Integrable (fun x => g₀ x z) μ ∧
        (fun x => g₀ x z) =ᵐ[μ.restrict sᶜ] 0 := by
  have : IsProbabilityMeasure (V.law.map V.zOf) :=
    Measure.isProbabilityMeasure_map V.measurable_z.aemeasurable
  have hmass : ∫⁻ p, ENNReal.ofReal (g₀ p.1 p.2)
      ∂μ.prod (V.law.map V.zOf) = 1 := by
    have hm := congrArg (fun m : Measure (X × Z) => m Set.univ) hIV.2.1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hm
    simpa only [Measure.map_apply_of_aemeasurable
      (V.measurable_x.prodMk V.measurable_z).aemeasurable MeasurableSet.univ,
      Set.preimage_univ, measure_univ, withDensity_apply,
      Measure.restrict_univ] using hm.symm
  obtain ⟨s, hs, hsf, hz⟩ := rdiv_density_sigmaFinite_restriction μ
    (V.law.map V.zOf) g₀ (hDensity.2 g₀ hDensity.1).1
    (hDensity.2 g₀ hDensity.1).2.1 hmass (hDensity.2 g₀ hDensity.1).2.2
  refine ⟨s, hs, hsf, ?_⟩
  filter_upwards [hz, rdiv_density_integrable_of_realizable V μ G g₀ g₀ hDensity
    hDensity.1] with z hz hi
  exact ⟨hi, hz⟩

/-- Suppose [the instrument space is the full instrument-measurable L² space, the
true density generates the joint input–instrument law, and the moment representer
gives the conditional outcome mean](hyp:hIV), [the density class contains the true density
and consists of measurable, nonnegative conditional densities normalized almost
everywhere](hyp:hDensity), [positive lower and upper density bounds hold on the
common support and all class densities vanish outside it](hyp:hBounds), [the selected
density maximizes preliminary-sample likelihood within the class](hyp:hMLE), and
[it has a jointly measurable version coherent with its population sections and
calibration evaluations](hyp:hSelectedDensityVersion). For [positive sample size
n](hyp:hn), [almost surely, at every calibration observation the selected density
section is integrable, nonnegative everywhere, and has input integral one](goal). -/
-- @node: rdiv_density_calibration_normalization
lemma rdiv_density_calibration_normalization (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z)) (c₀ CG : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split μ gHat)
    (n : ℕ) (hn : 0 < n) :
    ∀ᵐ ω ∂P, ∀ i ∈ split.cal n,
      Integrable (fun x => gHat n ω x (V.zOf (sample.Z i ω))) μ ∧
      (∀ x, 0 ≤ gHat n ω x (V.zOf (sample.Z i ω))) ∧
      (∫ x, gHat n ω x (V.zOf (sample.Z i ω)) ∂μ) = 1 := by
  obtain ⟨s, hs, hsf, hz⟩ := rdiv_true_density_sigmaFinite_restriction V μ G g₀
    hIV hDensity
  have : SigmaFinite (μ.restrict s) := hsf
  obtain ⟨gBar, hgBar, hgBarNonneg, hgBarSections, hgBarCalibration⟩ :=
    hSelectedDensityVersion n hn
  have hreduction (g : X → Z → ℝ) (hg : g ∈ G) (z : Z)
      (hiz : Integrable (fun x => g₀ x z) μ)
      (hzz : (fun x => g₀ x z) =ᵐ[μ.restrict sᶜ] 0) :
      Integrable (fun x => g x z) μ ∧
        (∫ x in s, g x z ∂μ) = ∫ x, g x z ∂μ :=
    rdiv_integral_restrict_of_density_domination μ s hs (fun x => g x z)
      (fun x => g₀ x z) (CG / c₀)
      (hDensity.2 g hg).1.of_uncurry_right.stronglyMeasurable.aestronglyMeasurable
      (fun x => (hDensity.2 g hg).2.1 x z) hiz
      (fun x => rdiv_density_ratio_of_bounds G g₀ g support c₀ CG hBounds
        hDensity.1 hg x z) hzz
  have hsections : ∀ᵐ ω ∂P, ∀ᵐ w ∂V.law,
      (∫ x in s, gHat n ω x (V.zOf w) ∂μ) = 1 := by
    filter_upwards [(hMLE n hn).1] with ω hω
    apply ae_of_ae_map (μ := V.law)
      (p := fun z => (∫ x in s, gHat n ω x z ∂μ) = 1) V.measurable_z.aemeasurable
    filter_upwards [hz, (hDensity.2 _ hω.1).2.2] with z hz hnorm
    exact (hreduction _ hω.1 z hz.1 hz.2).2.trans hnorm
  have hcal : ∀ᵐ ω ∂P, ∀ i ∈ split.cal n,
      (∫ x in s, gHat n ω x (V.zOf (sample.Z i ω)) ∂μ) = 1 := by
    have hbarSections : ∀ᵐ ω ∂P, ∀ᵐ w ∂V.law,
        (∫ x in s, gBar (ω, (x, V.zOf w)) ∂μ) = 1 := by
      filter_upwards [hsections, hgBarSections] with ω hω hcoherent
      have hw := ae_of_ae_map V.measurable_z.aemeasurable hcoherent
      filter_upwards [hω, hw] with w hw heq
      exact (integral_congr_ae (ae_restrict_of_ae heq)).trans hw
    have hrelation : MeasurableSet[(preliminarySigma V P sample split n).prod
        ‹MeasurableSpace 𝒲›]
        {p : Ω × 𝒲 | (∫ x in s, gBar (p.1, (x, V.zOf p.2)) ∂μ) = 1} := by
      let : MeasurableSpace Ω := preliminarySigma V P sample split n
      have hm : Measurable (fun p : (Ω × 𝒲) × X =>
          gBar (p.1.1, (p.2, V.zOf p.1.2))) := by
        have hzMeas := V.measurable_z
        fun_prop
      exact measurableSet_eq_fun hm.stronglyMeasurable.integral_prod_right'.measurable
        measurable_const
    have hbarCal := rdiv_calibration_ae_of_preliminary_sections V P sample split n
      (fun ω w => (∫ x in s, gBar (ω, (x, V.zOf w)) ∂μ) = 1)
      hrelation hbarSections
    filter_upwards [hbarCal, hgBarCalibration] with ω hω hcoherent
    intro i hi
    exact (integral_congr_ae (ae_restrict_of_ae (hcoherent i hi))).symm.trans (hω i hi)
  have hzcal : ∀ᵐ ω ∂P, ∀ i : ℕ,
      Integrable (fun x => g₀ x (V.zOf (sample.Z i ω))) μ ∧
        (fun x => g₀ x (V.zOf (sample.Z i ω))) =ᵐ[μ.restrict sᶜ] 0 := by
    apply (ae_all_iff).2
    intro i
    have hlaw : P.map (sample.Z i) = V.law := by
      rw [← (sample.identDist i).map_eq, sample.law]
    have hw := ae_of_ae_map V.measurable_z.aemeasurable hz
    rw [← hlaw] at hw
    exact ae_of_ae_map (sample.meas i).aemeasurable hw
  filter_upwards [(hMLE n hn).1, hcal, hzcal] with ω hω hcal hzcal
  intro i hi
  have hr := hreduction _ hω.1 _ (hzcal i).1 (hzcal i).2
  exact ⟨hr.1, fun x => (hDensity.2 _ hω.1).2.1 x _, hr.2.symm.trans (hcal i hi)⟩

/-- Suppose [the instrument space is the full instrument-measurable L² space, the
true density generates the joint input–instrument law, and the moment representer
gives the conditional outcome mean](hyp:hIV), [the density class contains the true density
and consists of measurable, nonnegative conditional densities normalized almost
everywhere](hyp:hDensity), [positive lower and upper density bounds hold on the
common support and all class densities vanish outside it](hyp:hBounds), [the selected
density maximizes preliminary-sample likelihood within the class](hyp:hMLE), and
[it has a jointly measurable version coherent with its population sections and
calibration evaluations](hyp:hSelectedDensityVersion). For [positive sample size
n](hyp:hn), [there is a measurable event of probability one on which the selected
density belongs to the class and its input integral equals one at every calibration
observation](goal). -/
-- @node: rdiv_density_calibration_event
lemma rdiv_density_calibration_event (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z)) (c₀ CG : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split μ gHat)
    (n : ℕ) (hn : 0 < n) :
    ∃ E : Set Ω, MeasurableSet E ∧ (∀ᵐ ω ∂P, ω ∈ E) ∧
      ∀ ω ∈ E, gHat n ω ∈ G ∧ ∀ i ∈ split.cal n,
        (∫ x, gHat n ω x (V.zOf (sample.Z i ω)) ∂μ) = 1 := by
  classical
  let good : Ω → Prop := fun ω => gHat n ω ∈ G ∧ ∀ i ∈ split.cal n,
    (∫ x, gHat n ω x (V.zOf (sample.Z i ω)) ∂μ) = 1
  have hgood : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [(hMLE n hn).1,
      rdiv_density_calibration_normalization
        (hSelectedDensityVersion := hSelectedDensityVersion) V P sample split μ G g₀ gHat support
        c₀ CG hIV hDensity hBounds hMLE n hn] with ω hω hnω
    exact ⟨hω.1, fun i hi => (hnω i hi).2.2⟩
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null hgood
  refine ⟨Nᶜ, hN.compl, ?_, ?_⟩
  · change P {ω | ω ∉ Nᶜ} = 0
    simpa using hN0
  · intro ω hω
    by_contra h
    exact hω (hsub h)

end Papers.TsAdaptiveEstimationInference
