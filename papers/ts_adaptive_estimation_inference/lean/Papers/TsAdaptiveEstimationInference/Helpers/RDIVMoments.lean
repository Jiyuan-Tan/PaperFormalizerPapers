module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVDensityReduction
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVDensityBounds
/-! Conditional density integration and input moments for the RDIV perturbation bound.
The sigma-finite restriction is derived from the true law; the original
dominating measure remains arbitrary. -/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter
open scoped ENNReal

variable {𝒲 X Z : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]
  [MeasurableSpace Z] (V : IVWorld 𝒲 X Z)

/-- If [the input restriction set is measurable](hyp:hs), [restricting the first
factor before taking the product gives the same measure as restricting the
product to that set in its first coordinate](goal). -/
-- @node: rdiv_restrict_first_prod
lemma rdiv_restrict_first_prod (μ : Measure X) (ν : Measure Z) [SFinite ν]
    (s : Set X) (hs : MeasurableSet s) :
    (μ.restrict s).prod ν = (μ.prod ν).restrict (s ×ˢ Set.univ) := by
  ext t ht
  rw [Measure.prod_apply ht, Measure.restrict_apply ht,
    Measure.prod_apply (ht.inter (hs.prod MeasurableSet.univ)),
    ← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx]

/-- Under [the conditional-density IV setting](hyp:hIV) and [density-class
realizability](hyp:hDensity), if [the joint test function is measurable](hyp:hf)
and [integrable under the joint input–instrument law](hyp:hfi), [its
density-weighted input sections are integrable almost everywhere, their
integrals are integrable over instruments, and their iterated integral equals
the test's expectation under the observation law](goal). -/
-- @node: rdiv_density_integral_disintegration
lemma rdiv_density_integral_disintegration (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (f : X × Z → ℝ) (hf : Measurable f)
    (hfi : Integrable f (V.law.map (fun w => (V.xOf w, V.zOf w)))) :
    (∀ᵐ z ∂V.law.map V.zOf, Integrable (fun x => f (x, z) * g₀ x z) μ) ∧
    Integrable (fun z => ∫ x, f (x, z) * g₀ x z ∂μ) (V.law.map V.zOf) ∧
    (∫ z, ∫ x, f (x, z) * g₀ x z ∂μ ∂V.law.map V.zOf) =
      ∫ w, f (V.xOf w, V.zOf w) ∂V.law := by
  have : IsProbabilityMeasure (V.law.map V.zOf) :=
    Measure.isProbabilityMeasure_map V.measurable_z.aemeasurable
  have : IsProbabilityMeasure (V.law.map (fun w => (V.xOf w, V.zOf w))) :=
    Measure.isProbabilityMeasure_map (V.measurable_x.prodMk V.measurable_z).aemeasurable
  have hg : Measurable (fun p : X × Z => g₀ p.1 p.2) := (hDensity.2 g₀ hDensity.1).1
  have hg0 := (hDensity.2 g₀ hDensity.1).2.1
  have htop : ∀ᵐ p ∂μ.prod (V.law.map V.zOf),
      ENNReal.ofReal (g₀ p.1 p.2) < ⊤ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hweighted : Integrable (fun p : X × Z => f p * g₀ p.1 p.2)
      (μ.prod (V.law.map V.zOf)) := by
    rw [hIV.2.1] at hfi
    have hi :=
      (integrable_withDensity_iff_integrable_smul' hg.ennreal_ofReal htop).1 hfi
    simpa only [Function.uncurry_def, smul_eq_mul,
      ENNReal.toReal_ofReal (hg0 _ _), mul_comm] using hi
  obtain ⟨s, hs, hsf, hz⟩ := rdiv_true_density_sigmaFinite_restriction V μ G g₀ hIV hDensity
  have : SigmaFinite (μ.restrict s) := hsf
  have hrestricted : Integrable (fun p : X × Z => f p * g₀ p.1 p.2)
      ((μ.restrict s).prod (V.law.map V.zOf)) := by
    rw [rdiv_restrict_first_prod μ _ s hs]
    exact hweighted.restrict
  have hsections : ∀ᵐ z ∂V.law.map V.zOf,
      Integrable (fun x => f (x, z) * g₀ x z) μ ∧
      (∫ x in s, f (x, z) * g₀ x z ∂μ) = ∫ x, f (x, z) * g₀ x z ∂μ := by
    filter_upwards [hz, hrestricted.prod_left_ae] with z hz hi
    have hzero : (fun x => f (x, z) * g₀ x z) =ᵐ[μ.restrict sᶜ] 0 := by
      filter_upwards [hz.2] with x hx
      simp only [hx, mul_zero, Pi.zero_apply]
    have hic : Integrable (fun x => f (x, z) * g₀ x z) (μ.restrict sᶜ) :=
      (integrable_zero X ℝ (μ.restrict sᶜ)).congr hzero.symm
    have hall : Integrable (fun x => f (x, z) * g₀ x z) μ := by
      rw [← integrableOn_univ, ← Set.union_compl_self s, integrableOn_union]
      exact ⟨hi, hic⟩
    refine ⟨hall, ?_⟩
    have hzint : (∫ x in sᶜ, f (x, z) * g₀ x z ∂μ) = 0 := by
      simpa using integral_congr_ae hzero
    simpa only [hzint, add_zero] using integral_add_compl hs hall
  have houter := hrestricted.integral_prod_right
  refine ⟨hsections.mono (fun _ h => h.1),
    houter.congr (hsections.mono (fun _ h => h.2)), ?_⟩
  calc
    _ = ∫ z, ∫ x in s, f (x, z) * g₀ x z ∂μ ∂V.law.map V.zOf :=
      integral_congr_ae (hsections.mono (fun _ h => h.2.symm))
    _ = ∫ p, f p * g₀ p.1 p.2 ∂(μ.restrict s).prod (V.law.map V.zOf) :=
      (integral_prod_symm _ hrestricted).symm
    _ = ∫ p, f p * g₀ p.1 p.2 ∂μ.prod (V.law.map V.zOf) := by
      rw [rdiv_restrict_first_prod μ _ s hs]
      have hgd : Integrable (fun p : X × Z => g₀ p.1 p.2)
          (μ.prod (V.law.map V.zOf)) := by
        have hi : Integrable (fun _ : X × Z => (1 : ℝ))
            (V.law.map (fun w => (V.xOf w, V.zOf w))) := by
          exact integrable_const _
        rw [hIV.2.1] at hi
        have hi' := (integrable_withDensity_iff_integrable_smul' hg.ennreal_ofReal htop).1 hi
        simpa only [Function.uncurry_def, smul_eq_mul, mul_one,
          ENNReal.toReal_ofReal (hg0 _ _)] using hi'
      have hgdall : (∫ p, g₀ p.1 p.2 ∂μ.prod (V.law.map V.zOf)) = 1 := by
        have he := integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal htop
          (fun _ : X × Z => (1 : ℝ))
        simp only [smul_eq_mul, mul_one,
          ENNReal.toReal_ofReal (hg0 _ _), ← hIV.2.1] at he
        simpa using he.symm
      have hgdr := hgd.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl :
        (μ.restrict s).prod (V.law.map V.zOf) ≤ μ.prod (V.law.map V.zOf))
      have hgdres : (∫ p, g₀ p.1 p.2 ∂(μ.restrict s).prod (V.law.map V.zOf)) = 1 := by
        rw [integral_prod_symm _ hgdr]
        have he : (fun z => ∫ x in s, g₀ x z ∂μ) =ᵐ[V.law.map V.zOf] fun _ => 1 := by
          filter_upwards [hz, (hDensity.2 g₀ hDensity.1).2.2] with z hz hn
          have hzc : (∫ x in sᶜ, g₀ x z ∂μ) = 0 := by
            simpa using integral_congr_ae hz.2
          linarith [integral_add_compl hs hz.1]
        rw [integral_congr_ae he]
        simp
      rw [rdiv_restrict_first_prod μ _ s hs] at hgdres
      have hgdz : (fun p : X × Z => g₀ p.1 p.2)
          =ᵐ[(μ.prod (V.law.map V.zOf)).restrict (s ×ˢ Set.univ)ᶜ] 0 := by
        apply (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun (p : X × Z) => hg0 p.1 p.2)
          hgd.integrableOn).1
        linarith [integral_add_compl (hs.prod MeasurableSet.univ) hgd]
      have hzero : (fun p : X × Z => f p * g₀ p.1 p.2)
          =ᵐ[(μ.prod (V.law.map V.zOf)).restrict (s ×ˢ Set.univ)ᶜ] 0 := by
        filter_upwards [hgdz] with p hp
        simp only [hp, mul_zero, Pi.zero_apply]
      have hi0 : (∫ p in (s ×ˢ (Set.univ : Set Z))ᶜ,
          f p * g₀ p.1 p.2 ∂μ.prod (V.law.map V.zOf)) = 0 := by
        simpa using integral_congr_ae hzero
      simpa only [hi0, add_zero] using
        integral_add_compl (hs.prod MeasurableSet.univ) hweighted
    _ = ∫ p, f p ∂(μ.prod (V.law.map V.zOf)).withDensity
        (fun p => ENNReal.ofReal (g₀ p.1 p.2)) := by
      rw [integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal htop f]
      simp only [smul_eq_mul, ENNReal.toReal_ofReal (hg0 _ _), mul_comm]
    _ = _ := by
      rw [← hIV.2.1]
      exact integral_map (V.measurable_x.prodMk V.measurable_z).aemeasurable
        hf.aestronglyMeasurable

/-- Under [the conditional-density IV setting](hyp:hIV) and [density-class
realizability](hyp:hDensity), if [the joint test is measurable](hyp:hf) and
[vanishes wherever the true conditional density is zero](hyp:hzf), [its input
integral is almost everywhere strongly measurable under the instrument
marginal](goal). -/
-- @node: rdiv_density_supported_integral_aestronglyMeasurable
@[fun_prop] lemma rdiv_density_supported_integral_aestronglyMeasurable (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (f : X × Z → ℝ) (hf : Measurable f)
    (hzf : ∀ x z, g₀ x z = 0 → f (x, z) = 0) :
    AEStronglyMeasurable (fun z => ∫ x, f (x, z) ∂μ) (V.law.map V.zOf) := by
  obtain ⟨s, hs, hsf, hz⟩ := rdiv_true_density_sigmaFinite_restriction V μ G g₀ hIV hDensity
  have : SigmaFinite (μ.restrict s) := hsf
  have hm : StronglyMeasurable (fun z => ∫ x in s, f (x, z) ∂μ) :=
    hf.stronglyMeasurable.integral_prod_left'
  apply hm.aestronglyMeasurable.congr
  filter_upwards [hz] with z hz
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [(ae_restrict_iff' hs.compl).1 hz.2] with x hx
  exact fun hxs => hzf x z (hx hxs)

/-- Under [the conditional-density IV setting](hyp:hIV) and [density-class
realizability](hyp:hDensity), for [a measurable input function](hyp:hu) with
[finite input second moment](hyp:hu2), [the density-weighted squared input is
integrable in almost every instrument section, its conditional second moment
is integrable, and averaging it gives the input second moment](goal). -/
-- @node: rdiv_density_input_second_moment
lemma rdiv_density_input_second_moment (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (u : X → ℝ) (hu : Measurable u) (hu2 : MemLp u 2 (V.law.map V.xOf)) :
    (∀ᵐ z ∂V.law.map V.zOf, Integrable (fun x => u x ^ 2 * g₀ x z) μ) ∧
    Integrable (fun z => ∫ x, u x ^ 2 * g₀ x z ∂μ) (V.law.map V.zOf) ∧
    (∫ z, ∫ x, u x ^ 2 * g₀ x z ∂μ ∂V.law.map V.zOf) =
      ∫ x, u x ^ 2 ∂V.law.map V.xOf := by
  have hf : Measurable (fun p : X × Z => u p.1 ^ 2) := by fun_prop
  have hi : Integrable (fun p : X × Z => u p.1 ^ 2)
      (V.law.map (fun w => (V.xOf w, V.zOf w))) := by
    apply (integrable_map_measure hf.aestronglyMeasurable
      (V.measurable_x.prodMk V.measurable_z).aemeasurable).2
    exact (integrable_map_measure (hu.pow_const 2).aestronglyMeasurable
      V.measurable_x.aemeasurable).1 hu2.integrable_sq
  obtain ⟨hsec, hint, heq⟩ := rdiv_density_integral_disintegration V μ G g₀ hIV hDensity
    (fun p => u p.1 ^ 2) hf hi
  refine ⟨hsec, hint, heq.trans ?_⟩
  exact (integral_map V.measurable_x.aemeasurable
    (hu.pow_const 2).aestronglyMeasurable).symm

/-- Under [the conditional-density IV setting](hyp:hIV), [density-class
realizability](hyp:hDensity), and [common-support density bounds](hyp:hBounds),
take [a density in the class](hyp:hg) and [a measurable input](hyp:hu) with
[finite second moment](hyp:hu2). If [the operator difference is almost
everywhere strongly measurable](hyp:hError) and [the conditional squared
Hellinger distance is integrable](hyp:hH), [the mean absolute operator error
is at most the input L2 norm times the square root of the mean squared
Hellinger distance, multiplied by the square root of twice one plus the
upper-to-lower density-bound ratio](goal). -/
-- @node: rdiv_density_operator_relative_input_bound
lemma rdiv_density_operator_relative_input_bound (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ g : X → Z → ℝ)
    (support : Set (X × Z)) (c₀ CG : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG) (hg : g ∈ G)
    (u : X → ℝ) (hu : Measurable u) (hu2 : MemLp u 2 (V.law.map V.xOf))
    (hError : AEStronglyMeasurable (densityOperator μ g u - densityOperator μ g₀ u)
      (V.law.map V.zOf))
    (hH : Integrable (fun z => hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z))
      (V.law.map V.zOf)) :
    inputL1Norm (V.law.map V.zOf) (densityOperator μ g u - densityOperator μ g₀ u) ≤
      Real.sqrt (2 * (CG / c₀ + 1)) * inputL2Norm (V.law.map V.xOf) u *
        Real.sqrt (∫ z, hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)
          ∂V.law.map V.zOf) := by
  obtain ⟨hsec, hint, heq⟩ := rdiv_density_input_second_moment V μ G g₀
    hIV hDensity u hu hu2
  have hratio := rdiv_density_ratio_of_bounds G g₀ g support c₀ CG
    hBounds hDensity.1 hg
  have hb := rdiv_density_operator_relative_bound μ (V.law.map V.zOf) g g₀ u
    (CG / c₀) (div_nonneg hBounds.2.1.le hBounds.1.le) hu.aestronglyMeasurable
    (by
      filter_upwards [rdiv_density_integrable_of_realizable V μ G g₀ g hDensity hg,
        rdiv_density_integrable_of_realizable V μ G g₀ g₀ hDensity hDensity.1,
        hsec] with z hgi hg₀i hmoment
      exact ⟨hgi, hg₀i, (fun x => (hDensity.2 g hg).2.1 x z),
        (fun x => (hDensity.2 g₀ hDensity.1).2.1 x z),
        ae_of_all _ (fun x => hratio x z), hmoment⟩)
    hError hint hH
  rw [heq] at hb
  exact hb

/-- Under [the conditional-density IV setting](hyp:hIV), [density-class
realizability](hyp:hDensity), and [common-support density bounds](hyp:hBounds),
take [a density in the class](hyp:hg) and [a measurable input](hyp:hu) with
[finite second moment](hyp:hu2). If [the rate constant is nonnegative](hyp:hC),
[the radius is nonnegative](hyp:hδ), and [the mean squared Hellinger distance
is at most the rate constant times the squared radius](hyp:hRate), [the mean
absolute operator error is at most the radius times the input L2 norm times
the square root of twice the rate constant times one plus the density-bound
ratio](goal). -/
-- @node: rdiv_density_operator_relative_input_rate
lemma rdiv_density_operator_relative_input_rate (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ g : X → Z → ℝ)
    (support : Set (X × Z)) (c₀ CG C δ : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG) (hg : g ∈ G)
    (u : X → ℝ) (hu : Measurable u) (hu2 : MemLp u 2 (V.law.map V.xOf))
    (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hRate : (∫ z, hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)
      ∂V.law.map V.zOf) ≤ C * δ ^ 2)
    :
    inputL1Norm (V.law.map V.zOf) (densityOperator μ g u - densityOperator μ g₀ u) ≤
      (Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt C) * δ *
        inputL2Norm (V.law.map V.xOf) u := by
  have hgz (x : X) (z : Z) (hx : g₀ x z = 0) : g x z = 0 := by
    have hdom := rdiv_density_ratio_of_bounds G g₀ g support c₀ CG
      hBounds hDensity.1 hg x z
    rw [hx, mul_zero] at hdom
    exact le_antisymm hdom ((hDensity.2 g hg).2.1 x z)
  have hgm : Measurable (Function.uncurry g) := (hDensity.2 g hg).1
  have hg₀m : Measurable (Function.uncurry g₀) := (hDensity.2 g₀ hDensity.1).1
  have hgint : AEStronglyMeasurable (densityOperator μ g u) (V.law.map V.zOf) :=
    rdiv_density_supported_integral_aestronglyMeasurable V μ G g₀ hIV hDensity
      (fun p => u p.1 * g p.1 p.2) ((hu.comp measurable_fst).mul hgm)
      (by intro x z hx; simp [hgz x z hx])
  have hg₀int : AEStronglyMeasurable (densityOperator μ g₀ u) (V.law.map V.zOf) :=
    rdiv_density_supported_integral_aestronglyMeasurable V μ G g₀ hIV hDensity
      (fun p => u p.1 * g₀ p.1 p.2) ((hu.comp measurable_fst).mul hg₀m)
      (by intro x z hx; simp [hx])
  have hError := hgint.sub hg₀int
  have hHm : AEStronglyMeasurable
      (fun z => hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z))
      (V.law.map V.zOf) := by
    apply rdiv_density_supported_integral_aestronglyMeasurable V μ G g₀ hIV hDensity
      (fun p => (Real.sqrt (g p.1 p.2) - Real.sqrt (g₀ p.1 p.2)) ^ 2)
    · exact (hgm.sqrt.sub hg₀m.sqrt).pow_const 2
    · intro x z hx
      simp [hx, hgz x z hx]
  have hb := rdiv_density_operator_relative_input_bound V μ G g₀ g support c₀ CG
    hIV hDensity hBounds hg u hu hu2 hError
    (rdiv_density_hellinger_integrable V μ G g₀ g hDensity hg hHm)
  have hs : Real.sqrt (∫ z, hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)
      ∂V.law.map V.zOf) ≤ Real.sqrt C * δ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hC]
    exact hRate
  calc
    _ ≤ Real.sqrt (2 * (CG / c₀ + 1)) * inputL2Norm (V.law.map V.xOf) u *
        (Real.sqrt C * δ) := hb.trans (mul_le_mul_of_nonneg_left hs (by
          unfold inputL2Norm
          positivity))
    _ = _ := by ring

/-- For [a primal Hilbert-space element](hyp:h), [its chosen input realization
has finite second moment and its input L2 norm equals the element's Hilbert
norm](goal). -/
-- @node: rdiv_primal_input_memLp_norm
lemma rdiv_primal_input_memLp_norm (h : V.Hbar.toSubmodule) :
    MemLp (primalVersion V h) 2 (V.law.map V.xOf) ∧
      inputL2Norm (V.law.map V.xOf) (primalVersion V h) = ‖h‖ := by
  have hm : Measurable (primalVersion V h) := V.primal_measurable h
  have hp : MemLp (fun w => primalVersion V h (V.xOf w)) 2 V.law :=
    (memLp_congr_ae (V.primal_coherent h)).2 (Lp.memLp (h : Lp ℝ 2 V.law))
  refine ⟨(memLp_map_measure_iff hm.aestronglyMeasurable V.measurable_x.aemeasurable).2 hp, ?_⟩
  have he : (∫ x, primalVersion V h x ^ 2 ∂V.law.map V.xOf) = ‖h‖ ^ 2 := by
    rw [integral_map V.measurable_x.aemeasurable (hm.pow_const 2).aestronglyMeasurable]
    calc
      _ = ∫ w, ((h : Lp ℝ 2 V.law) w) ^ 2 ∂V.law := by
        apply integral_congr_ae
        filter_upwards [V.primal_coherent h] with w hw
        exact congrArg (fun x : ℝ => x ^ 2) hw
      _ = _ := by
        simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two,
          Submodule.norm_coe] using (real_inner_self_eq_norm_sq (h : Lp ℝ 2 V.law))
  unfold inputL2Norm
  rw [he, Real.sqrt_sq (norm_nonneg h)]

/-- Under [the conditional-density IV setting](hyp:hIV), [density-class
realizability](hyp:hDensity), and [common-support density bounds](hyp:hBounds),
take [a density in the class](hyp:hg) and [a primal Hilbert-space element](hyp:h).
If [the rate constant is nonnegative](hyp:hC), [the radius is nonnegative](hyp:hδ),
and [the mean squared Hellinger distance is at most the rate constant times
the squared radius](hyp:hRate), [the mean absolute density-operator error is
at most the element's norm times the radius times the square root of twice
the rate constant times one plus the density-bound ratio](goal). -/
-- @node: rdiv_hypothesis_operator_relative_rate
lemma rdiv_hypothesis_operator_relative_rate (μ : Measure X)
    (G : Set (X → Z → ℝ)) (g₀ g : X → Z → ℝ)
    (support : Set (X × Z)) (c₀ CG C δ : ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG) (hg : g ∈ G)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hRate : (∫ z, hellingerSqDensity μ (fun x => g x z) (fun x => g₀ x z)
      ∂V.law.map V.zOf) ≤ C * δ ^ 2) (h : V.Hbar.toSubmodule) :
    inputL1Norm (V.law.map V.zOf)
      (densityOperator μ g (primalVersion V h) - densityOperator μ g₀ (primalVersion V h)) ≤
      (Real.sqrt (2 * (CG / c₀ + 1)) * Real.sqrt C) * δ * ‖h‖ := by
  obtain ⟨hmem, hnorm⟩ := rdiv_primal_input_memLp_norm V h
  have hb := rdiv_density_operator_relative_input_rate V μ G g₀ g support c₀ CG C δ
    hIV hDensity hBounds hg (primalVersion V h) (V.primal_measurable h) hmem hC hδ hRate
  rwa [hnorm] at hb

end Papers.TsAdaptiveEstimationInference
