module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVSelectedKernel
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVOperatorRestriction
/-! Change of measure for the selected-L2 density integral.

The cancellation is proved under the reference measure, including its zero-density
set. Coherence of a primal realization is used only after fixing an L2 vector;
no joint measurability of the supplied primal evaluations is required.
-/
public section
set_option linter.style.haveILetI false

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter

variable {X W Z A : Type*} [MeasurableSpace X] [MeasurableSpace W]
  [MeasurableSpace Z] [MeasurableSpace A]

/-- If [the instrumental-variable model has true conditional density g₀ relative to μ](hyp:hIV) and [g₀ belongs to a class of measurable, nonnegative, normalized conditional densities](hyp:hDensity), then [there is a measurable input set on which μ is sigma-finite and the same instrumental-variable model remains valid, while for almost every instrument value the true density section is integrable under μ and vanishes almost everywhere outside that set](goal). -/
-- @node: rdiv_true_joint_on_sigmaFinite_restriction
lemma rdiv_true_joint_on_sigmaFinite_restriction (V : IVWorld W X Z)
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀) :
    ∃ s : Set X, MeasurableSet s ∧ SigmaFinite (μ.restrict s) ∧
      RDIVSetting V (μ.restrict s) g₀ ∧
      ∀ᵐ z ∂V.law.map V.zOf, Integrable (fun x => g₀ x z) μ ∧
        (fun x => g₀ x z) =ᵐ[μ.restrict sᶜ] 0 := by
  obtain ⟨s, hs, hsf, hz⟩ :=
    rdiv_true_density_sigmaFinite_restriction V μ G g₀ hIV hDensity
  let : SigmaFinite (μ.restrict s) := hsf
  let : IsProbabilityMeasure (V.law.map V.zOf) :=
    Measure.isProbabilityMeasure_map V.measurable_z.aemeasurable
  let joint : Measure (X × Z) := ((μ.restrict s).prod (V.law.map V.zOf)).withDensity
    (fun q => ENNReal.ofReal (g₀ q.1 q.2))
  have hnorm : ∀ᵐ z ∂V.law.map V.zOf, ∫⁻ x in s, ENNReal.ofReal (g₀ x z) ∂μ = 1 := by
    filter_upwards [hz, (hDensity.2 g₀ hDensity.1).2.2] with z hz hnorm
    have hzero : ∫ x in sᶜ, g₀ x z ∂μ = 0 := by
      simpa using integral_congr_ae hz.2
    have he : ∫ x in s, g₀ x z ∂μ = 1 := by
      linarith [integral_add_compl hs hz.1]
    rw [← ofReal_integral_eq_lintegral_ofReal hz.1.restrict
      (ae_of_all _ fun x => (hDensity.2 g₀ hDensity.1).2.1 x z), he]
    simp
  have hmass : joint Set.univ = 1 := by
    dsimp only [joint]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc
      _ = ∫⁻ z, ∫⁻ x in s, ENNReal.ofReal (g₀ x z) ∂μ ∂V.law.map V.zOf :=
        lintegral_prod_symm _ (hDensity.2 g₀ hDensity.1).1.ennreal_ofReal.aemeasurable
      _ = 1 := by rw [lintegral_congr_ae hnorm]; simp
  have hle : joint ≤ V.law.map (fun w => (V.xOf w, V.zOf w)) := by
    rw [hIV.2.1]
    apply Measure.le_iff.mpr
    intro t ht
    dsimp only [joint]
    rw [withDensity_apply _ ht, withDensity_apply _ ht]
    exact lintegral_mono' (Measure.restrict_mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl) t) le_rfl
  let : IsProbabilityMeasure joint := ⟨hmass⟩
  let : IsProbabilityMeasure (V.law.map (fun w => (V.xOf w, V.zOf w))) :=
    Measure.isProbabilityMeasure_map (V.measurable_x.prodMk V.measurable_z).aemeasurable
  have heq : joint = V.law.map (fun w => (V.xOf w, V.zOf w)) :=
    Measure.eq_of_le_of_isProbabilityMeasure hle
  exact ⟨s, hs, hsf, ⟨hIV.1, heq.symm, hIV.2.2⟩, hz⟩

/-- On a sigma-finite reference measure μ, if [the instrumental-variable model has true conditional density g₀ relative to μ](hyp:hIV), then [the input marginal has a measurable, everywhere nonnegative real density relative to μ](goal). -/
-- @node: rdiv_input_marginal_real_density
lemma rdiv_input_marginal_real_density (V : IVWorld W X Z)
    (μ : Measure X) [SigmaFinite μ] (g₀ : X → Z → ℝ)
    (hIV : RDIVSetting V μ g₀) :
    ∃ p : X → ℝ, Measurable p ∧ (∀ x, 0 ≤ p x) ∧
      V.law.map V.xOf = μ.withDensity (fun x => ENNReal.ofReal (p x)) := by
  let : IsProbabilityMeasure (V.law.map V.zOf) :=
    Measure.isProbabilityMeasure_map V.measurable_z.aemeasurable
  let : IsProbabilityMeasure (V.law.map V.xOf) :=
    Measure.isProbabilityMeasure_map V.measurable_x.aemeasurable
  have hac : V.law.map V.xOf ≪ μ := by
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hnull
    have hrect : Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set Z) := by
      ext q
      simp
    have hprod : (μ.prod (V.law.map V.zOf)) (Prod.fst ⁻¹' s) = 0 := by
      rw [hrect, Measure.prod_prod, hnull, zero_mul]
    have hj := withDensity_absolutelyContinuous (μ.prod (V.law.map V.zOf))
      (fun q => ENNReal.ofReal (g₀ q.1 q.2)) hprod
    rw [← hIV.2.1, Measure.map_apply (V.measurable_x.prodMk V.measurable_z)
      (measurable_fst hs)] at hj
    rw [Measure.map_apply V.measurable_x hs]
    exact hj
  let p : X → ℝ := fun x => ((V.law.map V.xOf).rnDeriv μ x).toReal
  refine ⟨p, (Measure.measurable_rnDeriv _ _).ennreal_toReal,
    fun _ => ENNReal.toReal_nonneg, ?_⟩
  symm
  calc
    _ = μ.withDensity ((V.law.map V.xOf).rnDeriv μ) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top (V.law.map V.xOf) μ] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    _ = _ := Measure.withDensity_rnDeriv_eq _ _ hac

/-- If [a real density p is measurable](hyp:hp), then [p is nonzero almost everywhere under the measure obtained by weighting μ by the nonnegative part of p](goal). -/
-- @node: rdiv_marginal_density_ne_zero
lemma rdiv_marginal_density_ne_zero (μ : Measure X) (p : X → ℝ)
    (hp : Measurable p) :
    ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (p x)), p x ≠ 0 := by
  apply (ae_withDensity_iff hp.ennreal_ofReal).2
  exact ae_of_all _ fun x hx hpx => hx (by simp [hpx])

/-- For an s-finite reference measure μ, suppose [g₀ is jointly measurable](hyp:hg₀), [g₀ is everywhere nonnegative](hyp:hg₀0), [the true joint law has density g₀ relative to μ times the instrument marginal](hyp:hjoint), [p is measurable](hyp:hp), and [the input marginal has density equal to the nonnegative part of p relative to μ](hyp:hmap). Then [for almost every instrument value, g₀ vanishes μ-almost everywhere that p is zero](goal). -/
-- @node: rdiv_density_sections_ignore_marginal_zero
lemma rdiv_density_sections_ignore_marginal_zero (V : IVWorld W X Z)
    (μ : Measure X) [SFinite μ] (g₀ : X → Z → ℝ)
    (hg₀ : Measurable (Function.uncurry g₀)) (hg₀0 : ∀ x z, 0 ≤ g₀ x z)
    (hjoint : V.law.map (fun w => (V.xOf w, V.zOf w)) =
      (μ.prod (V.law.map V.zOf)).withDensity (fun q => ENNReal.ofReal (g₀ q.1 q.2)))
    (p : X → ℝ) (hp : Measurable p)
    (hmap : V.law.map V.xOf = μ.withDensity (fun x => ENNReal.ofReal (p x))) :
    ∀ᵐ z ∂V.law.map V.zOf, ∀ᵐ x ∂μ, p x = 0 → g₀ x z = 0 := by
  letI : IsProbabilityMeasure (V.law.map V.zOf) :=
    Measure.isProbabilityMeasure_map V.measurable_z.aemeasurable
  have hx : ∀ᵐ x ∂V.law.map V.xOf, p x ≠ 0 := by
    rw [hmap]
    exact rdiv_marginal_density_ne_zero μ p hp
  have hw : ∀ᵐ w ∂V.law, p (V.xOf w) ≠ 0 :=
    ae_of_ae_map V.measurable_x.aemeasurable hx
  have hj : ∀ᵐ q ∂V.law.map (fun w => (V.xOf w, V.zOf w)), p q.1 ≠ 0 :=
    (ae_map_iff (V.measurable_x.prodMk V.measurable_z).aemeasurable
      (measurableSet_eq_fun (hp.comp measurable_fst) measurable_const).compl).2 hw
  rw [hjoint] at hj
  have hprod : ∀ᵐ q ∂μ.prod (V.law.map V.zOf), p q.1 = 0 → g₀ q.1 q.2 = 0 := by
    filter_upwards [(ae_withDensity_iff hg₀.ennreal_ofReal).1 hj] with q hq hpq
    by_contra hgq
    exact hq (by
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (hg₀0 _ _) (Ne.symm hgq)))) hpq
  have hmeas : MeasurableSet {q : X × Z | p q.1 = 0 → g₀ q.1 q.2 = 0} := by
    have he : {q : X × Z | p q.1 = 0 → g₀ q.1 q.2 = 0} =
        {q : X × Z | p q.1 = 0}ᶜ ∪ {q : X × Z | g₀ q.1 q.2 = 0} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
      tauto
    rw [he]
    exact (measurableSet_eq_fun (hp.comp measurable_fst) measurable_const).compl.union
      (measurableSet_eq_fun hg₀ measurable_const)
  exact (Measure.ae_ae_comm hmeas).1 (Measure.ae_ae_of_ae_prod hprod)

/-- Suppose [G contains the true density and consists of measurable, nonnegative, normalized conditional densities](hyp:hDensity), [G and the true density satisfy common support and lower and upper bounds](hyp:hBounds), and [for almost every instrument value the true density vanishes μs-almost everywhere that p is zero](hyp:hz). Then [on a single event of full instrument-marginal probability, every density in G vanishes μs-almost everywhere that p is zero](goal). -/
-- @node: rdiv_density_class_ignores_marginal_zero
lemma rdiv_density_class_ignores_marginal_zero (V : IVWorld W X Z)
    (μ μs : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (support : Set (X × Z)) (c₀ CG : ℝ)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (p : X → ℝ)
    (hz : ∀ᵐ z ∂V.law.map V.zOf, ∀ᵐ x ∂μs, p x = 0 → g₀ x z = 0) :
    ∀ᵐ z ∂V.law.map V.zOf, ∀ g ∈ G,
      ∀ᵐ x ∂μs, p x = 0 → g x z = 0 := by
  filter_upwards [hz] with z hz
  intro g hg
  filter_upwards [hz] with x hx
  intro hpx
  apply le_antisymm _ ((hDensity.2 g hg).2.1 x z)
  calc
    g x z ≤ (CG / c₀) * g₀ x z :=
      rdiv_density_ratio_of_bounds G g₀ g support c₀ CG hBounds hDensity.1 hg x z
    _ = 0 := by rw [hx hpx, mul_zero]

/-- If [p is measurable](hyp:hp), [p is everywhere nonnegative](hyp:hp0), [u is integrable under μ](hyp:hu), and [u vanishes μ-almost everywhere that p is zero](hyp:hz), then [u divided by p is integrable under the measure with density p relative to μ, and its integral under that measure equals the integral of u under μ](goal). -/
-- @node: rdiv_inverse_density_integral
lemma rdiv_inverse_density_integral (μ : Measure X) (p u : X → ℝ)
    (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x)
    (hu : Integrable u μ) (hz : ∀ᵐ x ∂μ, p x = 0 → u x = 0) :
    Integrable (fun x => u x / p x)
        (μ.withDensity (fun x => ENNReal.ofReal (p x))) ∧
      (∫ x, u x / p x ∂μ.withDensity (fun x => ENNReal.ofReal (p x))) =
        ∫ x, u x ∂μ := by
  have he : (fun x => (ENNReal.ofReal (p x)).toReal • (u x / p x)) =ᵐ[μ] u := by
    filter_upwards [hz] with x hx
    rw [ENNReal.toReal_ofReal (hp0 x), smul_eq_mul]
    by_cases hpx : p x = 0
    · simp [hpx, hx hpx]
    · field_simp
  refine ⟨(integrable_withDensity_iff_integrable_smul' hp.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).2 (hu.congr he.symm), ?_⟩
  rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  exact integral_congr_ae he

/-- Suppose [p is measurable](hyp:hp), [p is everywhere nonnegative](hyp:hp0), [g is measurable](hyp:hg), [the input marginal has density p relative to μ](hyp:hmap), and [g vanishes μ-almost everywhere that p is zero](hyp:hz). For [a fixed vector h in the closed hypothesis space](hyp:h), if [its input-space realization times g is integrable under μ](hyp:hi), then [its observation-space representative times g divided by p at the observed input is integrable under the observation law, and that integral equals the μ-integral of its input-space realization times g](goal). -/
-- @node: rdiv_primal_inverse_density_integral
lemma rdiv_primal_inverse_density_integral (V : IVWorld W X Z)
    (μ : Measure X) (p g : X → ℝ)
    (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hg : Measurable g)
    (hmap : V.law.map V.xOf = μ.withDensity (fun x => ENNReal.ofReal (p x)))
    (hz : ∀ᵐ x ∂μ, p x = 0 → g x = 0)
    (h : V.Hbar.toSubmodule)
    (hi : Integrable (fun x => primalVersion V h x * g x) μ) :
    Integrable (fun w => (h : Lp ℝ 2 V.law) w * (g (V.xOf w) / p (V.xOf w)))
        V.law ∧
      (∫ w, (h : Lp ℝ 2 V.law) w * (g (V.xOf w) / p (V.xOf w)) ∂V.law) =
        ∫ x, primalVersion V h x * g x ∂μ := by
  obtain ⟨hint, heq⟩ := rdiv_inverse_density_integral μ p
    (fun x => primalVersion V h x * g x) hp hp0 hi
    (hz.mono fun x hx hpx => by rw [hx hpx, mul_zero])
  let q : X → ℝ := fun x => primalVersion V h x * (g x / p x)
  have hq : Measurable q := (V.primal_measurable h).mul (hg.div hp)
  have hqi : Integrable q (V.law.map V.xOf) := by
    rw [hmap]
    simpa only [q, mul_div_assoc] using hint
  have hcoh : (fun w => q (V.xOf w)) =ᵐ[V.law]
      (fun w => (h : Lp ℝ 2 V.law) w * (g (V.xOf w) / p (V.xOf w))) := by
    filter_upwards [V.primal_coherent h] with w hw
    exact congrArg (fun y => y * (g (V.xOf w) / p (V.xOf w))) hw
  refine ⟨((integrable_map_measure hq.aestronglyMeasurable
    V.measurable_x.aemeasurable).1 hqi).congr hcoh, ?_⟩
  calc
    _ = ∫ w, q (V.xOf w) ∂V.law := integral_congr_ae hcoh.symm
    _ = ∫ x, q x ∂V.law.map V.xOf :=
      (integral_map V.measurable_x.aemeasurable hq.aestronglyMeasurable).symm
    _ = _ := by simpa only [hmap, q, mul_div_assoc] using heq

/-- Suppose [p is measurable](hyp:hp), [p is everywhere nonnegative](hyp:hp0), [the input marginal has density p relative to μ](hyp:hmap), [the selection F into the closed hypothesis space is Borel measurable](hyp:hF), [the parameter-dependent density g is jointly measurable](hyp:hg), and [g is everywhere nonnegative](hyp:hg0). Then [there is a jointly measurable operator in the selection parameter and instrument value that equals the μ-integral of the selected vector's input-space realization times g at every parameter and instrument value where g vanishes almost everywhere on the zero set of p and that product is integrable](goal). -/
-- @node: rdiv_selected_operator_version_of_marginal_density
lemma rdiv_selected_operator_version_of_marginal_density (V : IVWorld W X Z)
    (μ : Measure X) (p : X → ℝ)
    (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x)
    (hmap : V.law.map V.xOf = μ.withDensity (fun x => ENNReal.ofReal (p x)))
    (F : A → V.Hbar.toSubmodule)
    (hF : @Measurable A V.Hbar.toSubmodule inferInstance (borel _) F)
    (g : A × (X × Z) → ℝ) (hg : Measurable g) (hg0 : ∀ a x z, 0 ≤ g (a, (x, z))) :
    ∃ op : A → Z → ℝ, Measurable (Function.uncurry op) ∧
      ∀ a z, (∀ᵐ x ∂μ, p x = 0 → g (a, (x, z)) = 0) →
        Integrable (fun x => primalVersion V (F a) x * g (a, (x, z))) μ →
        op a z = ∫ x, primalVersion V (F a) x * g (a, (x, z)) ∂μ := by
  letI : MeasurableSpace (Lp ℝ 2 V.law) := borel _
  let : BorelSpace (Lp ℝ 2 V.law) := ⟨rfl⟩
  letI : MeasurableSpace V.Hbar.toSubmodule := borel _
  let : BorelSpace V.Hbar.toSubmodule := ⟨rfl⟩
  let L : A × Z → Lp ℝ 2 V.law := fun a => (F a.1 : Lp ℝ 2 V.law)
  let weight : (A × Z) × W → ℝ := fun a =>
    g (a.1.1, (V.xOf a.2, a.1.2)) / p (V.xOf a.2)
  have hL : Measurable L :=
    (continuous_subtype_val.measurable.comp hF).comp measurable_fst
  have hw : Measurable weight := by
    exact (hg.comp (measurable_fst.fst.prodMk
      ((V.measurable_x.comp measurable_snd).prodMk measurable_fst.snd))).div
        (hp.comp (V.measurable_x.comp measurable_snd))
  let op : A → Z → ℝ := fun a z => rdivSelectedL2Integral V.law L weight (a, z)
  refine ⟨op, rdivSelectedL2Integral_measurable V.law hL hw, ?_⟩
  intro a z hz hi
  have hgz : Measurable (fun x => g (a, (x, z))) := by fun_prop
  obtain ⟨hint, heq⟩ := rdiv_primal_inverse_density_integral V μ p
    (fun x => g (a, (x, z))) hp hp0 hgz hmap hz (F a) hi
  exact (rdivSelectedL2Integral_eq V.law L weight (a, z)
    (hw.comp (measurable_const.prodMk measurable_id))
    (fun w => div_nonneg (hg0 a _ z) (hp0 _)) hint).trans heq

/-- Suppose [the instrumental-variable model has true conditional density g₀ relative to μ](hyp:hIV), [the density class contains g₀ and consists of measurable, nonnegative, normalized conditional densities](hyp:hDensity), [the densities satisfy common support and lower and upper bounds](hyp:hBounds), [the hypothesis class is bounded on that support](hyp:hHyp), [the fitted density is a selected likelihood maximizer](hyp:hMLE), and [it admits the specified measurable density version with agreement at calibration observations](hyp:hSelectedDensityVersion). At [a positive sample size](hyp:hn), if [every grid candidate belongs to the hypothesis class for every sample outcome](hyp:hCandidate) and [each grid candidate is a Borel measurable selection using the preliminary and fitting observations](hyp:hMeas), then [there is an operator family jointly measurable in those training observations and the instrument at each grid penalty, together with a measurable event of full probability on which the family agrees with the estimated operator both almost everywhere under the instrument marginal and at every calibration observation, simultaneously over the grid](goal). -/
-- @node: rdiv_selected_family_operator_calibration_version
lemma rdiv_selected_family_operator_calibration_version
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (V : IVWorld W X Z) (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG ρ : ℝ) (candidate : ℝ → Ω → V.Hbar.toSubmodule)
    (hIV : RDIVSetting V μ g₀) (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split μ gHat)
    (n : ℕ) (hn : 0 < n)
    (hCandidate : ∀ lam ∈ regGrid ρ n, ∀ ω, candidate lam ω ∈ V.H)
    (hMeas : ∀ lam ∈ regGrid ρ n, @Measurable Ω V.Hbar.toSubmodule
      (⨆ i ∈ split.pre n ∪ split.fit n,
        MeasurableSpace.comap (sample.Z i) inferInstance) (borel _) (candidate lam)) :
    ∃ op : ℝ → Ω → Z → ℝ,
      (∀ lam ∈ regGrid ρ n, @Measurable (Ω × Z) ℝ
        ((⨆ i ∈ split.pre n ∪ split.fit n,
          MeasurableSpace.comap (sample.Z i) inferInstance).prod inferInstance)
        inferInstance (fun p => op lam p.1 p.2)) ∧
      ∃ N : Set Ω, MeasurableSet N ∧ (∀ᵐ ω ∂P, ω ∈ N) ∧
        ∀ ω ∈ N, ∀ lam ∈ regGrid ρ n,
          (op lam ω =ᵐ[V.law.map V.zOf]
            estimatedOperator V μ gHat n ω (candidate lam ω)) ∧
          (∀ i ∈ split.cal n, op lam ω (V.zOf (sample.Z i ω)) =
            estimatedOperator V μ gHat n ω (candidate lam ω)
              (V.zOf (sample.Z i ω))) := by
  classical
  obtain ⟨s, hs, hsf, hIVs, hsections⟩ :=
    rdiv_true_joint_on_sigmaFinite_restriction V μ G g₀ hIV hDensity
  let : SigmaFinite (μ.restrict s) := hsf
  obtain ⟨p, hp, hp0, hmap⟩ := rdiv_input_marginal_real_density V (μ.restrict s) g₀ hIVs
  have hzero := rdiv_density_sections_ignore_marginal_zero V (μ.restrict s) g₀
    (hDensity.2 g₀ hDensity.1).1 (hDensity.2 g₀ hDensity.1).2.1 hIVs.2.1 p hp hmap
  have hzeroAll := rdiv_density_class_ignores_marginal_zero V μ (μ.restrict s)
    G g₀ support c₀ CG hDensity hBounds p hzero
  let good : Z → Prop := fun z =>
    (Integrable (fun x => g₀ x z) μ ∧ (fun x => g₀ x z) =ᵐ[μ.restrict sᶜ] 0) ∧
      ∀ g ∈ G, ∀ᵐ x ∂μ.restrict s, p x = 0 → g x z = 0
  have hgood : ∀ᵐ z ∂V.law.map V.zOf, good z := hsections.and hzeroAll
  have hgoodActual : ∀ᵐ ω ∂P, ∀ i : ℕ, good (V.zOf (sample.Z i ω)) := by
    apply ae_all_iff.mpr
    intro i
    have hw := ae_of_ae_map V.measurable_z.aemeasurable hgood
    rw [← sample.map_eq i] at hw
    exact ae_of_ae_map (sample.meas i).aemeasurable hw
  obtain ⟨gBar, hgBar, hgBar0, hgBarSections, hgBarActual⟩ :=
    hSelectedDensityVersion n hn
  let mt := ⨆ i ∈ split.pre n ∪ split.fit n,
    MeasurableSpace.comap (sample.Z i) inferInstance
  letI : MeasurableSpace Ω := mΩ
  have hpre : preliminarySigma V P sample split n ≤ mt := by
    apply iSup_le
    intro i
    apply iSup_le
    intro hi
    exact le_iSup_of_le i (le_iSup_of_le (Finset.mem_union_left _ hi) le_rfl)
  have hversions (lam : ℝ) (hlam : lam ∈ regGrid ρ n) :
      ∃ f : Ω → Z → ℝ,
        @Measurable (Ω × Z) ℝ (mt.prod inferInstance) inferInstance
          (Function.uncurry f) ∧
        ∀ ω z, (∀ᵐ x ∂μ.restrict s, p x = 0 → gBar (ω, (x, z)) = 0) →
          Integrable (fun x => primalVersion V (candidate lam ω) x *
            gBar (ω, (x, z))) (μ.restrict s) →
          f ω z = ∫ x in s, primalVersion V (candidate lam ω) x *
            gBar (ω, (x, z)) ∂μ := by
    have hF := hMeas lam hlam
    letI : MeasurableSpace Ω := mt
    have hg : Measurable gBar := hgBar.comp
      ((measurable_fst.mono le_rfl hpre).prodMk measurable_snd)
    exact rdiv_selected_operator_version_of_marginal_density V (μ.restrict s) p
      hp hp0 hmap (candidate lam) hF
      gBar hg (fun ω x z => hgBar0 (ω, (x, z)))
  let op : ℝ → Ω → Z → ℝ := fun lam =>
    if hlam : lam ∈ regGrid ρ n then (hversions lam hlam).choose else fun _ _ => 0
  have hop (lam : ℝ) (hlam : lam ∈ regGrid ρ n) :
      op lam = (hversions lam hlam).choose := by simp only [op, dif_pos hlam]
  have hHyp' : HypothesisClassBounded V support (max B 0) := by
    intro h hh q hq
    exact (hHyp h hh q hq).trans (le_max_left _ _)
  have hidentify (lam : ℝ) (hlam : lam ∈ regGrid ρ n) (ω : Ω) (z : Z)
      (hg : gHat n ω ∈ G) (hz : good z)
      (heq : (fun x => gBar (ω, (x, z))) =ᵐ[μ] (fun x => gHat n ω x z)) :
      op lam ω z = estimatedOperator V μ gHat n ω (candidate lam ω) z := by
    have hh : candidate lam ω ∈ V.H := hCandidate lam hlam ω
    obtain ⟨hi, hrestrict⟩ := rdiv_density_operator_integral_restrict V μ s hs G g₀
      support (max B 0) c₀ CG hDensity hBounds hHyp' (le_max_right _ _)
      z hz.1.1 hz.1.2 (gHat n ω) hg (candidate lam ω) hh
    have heqs := ae_restrict_of_ae (s := s) heq
    have hprod : (fun x => primalVersion V (candidate lam ω) x * gBar (ω, (x, z)))
        =ᵐ[μ.restrict s] (fun x => primalVersion V (candidate lam ω) x * gHat n ω x z) :=
      heqs.mono fun x hx => congrArg (fun y => primalVersion V (candidate lam ω) x * y) hx
    have hbarZero : ∀ᵐ x ∂μ.restrict s, p x = 0 → gBar (ω, (x, z)) = 0 := by
      filter_upwards [hz.2 (gHat n ω) hg, heqs] with x hx heq
      intro hpx
      exact heq.trans (hx hpx)
    rw [hop lam hlam]
    exact ((hversions lam hlam).choose_spec.2 ω z hbarZero
      (hi.restrict.congr hprod.symm)).trans ((integral_congr_ae hprod).trans hrestrict)
  have hall : ∀ᵐ ω ∂P, ∀ lam ∈ regGrid ρ n,
      (op lam ω =ᵐ[V.law.map V.zOf]
        estimatedOperator V μ gHat n ω (candidate lam ω)) ∧
      ∀ i ∈ split.cal n, op lam ω (V.zOf (sample.Z i ω)) =
        estimatedOperator V μ gHat n ω (candidate lam ω) (V.zOf (sample.Z i ω)) := by
    filter_upwards [(hMLE n hn).1, hgBarSections, hgBarActual, hgoodActual]
      with ω hg hsections hactual hgoodActual
    intro lam hlam
    constructor
    · filter_upwards [hgood, hsections] with z hz heq
      exact hidentify lam hlam ω z hg.1 hz heq
    · intro i hi
      exact hidentify lam hlam ω _ hg.1 (hgoodActual i) (hactual i hi)
  obtain ⟨N, hsub, hN, hNzero⟩ := exists_measurable_superset_of_null
    (show P {ω | ¬ ∀ lam ∈ regGrid ρ n,
      (op lam ω =ᵐ[V.law.map V.zOf]
        estimatedOperator V μ gHat n ω (candidate lam ω)) ∧
      ∀ i ∈ split.cal n, op lam ω (V.zOf (sample.Z i ω)) =
        estimatedOperator V μ gHat n ω (candidate lam ω) (V.zOf (sample.Z i ω))} = 0
      from hall)
  refine ⟨op, ?_, Nᶜ, hN.compl, ?_, ?_⟩
  · intro lam hlam
    rw [hop lam hlam]
    exact (hversions lam hlam).choose_spec.1
  · exact compl_mem_ae_iff.mpr hNzero
  · intro ω hω
    by_contra h
    exact hω (hsub h)

end Papers.TsAdaptiveEstimationInference
