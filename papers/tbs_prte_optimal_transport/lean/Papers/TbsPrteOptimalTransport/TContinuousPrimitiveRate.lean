module
public import Papers.TbsPrteOptimalTransport.Helpers.ContinuousLearners
public import Papers.TbsPrteOptimalTransport.Helpers.FirstStageTransfer
public import Papers.TbsPrteOptimalTransport.Helpers.RegressionTransfer
public import Papers.TbsPrteOptimalTransport.Helpers.PrimitivePluginTransfer
public import Papers.TbsPrteOptimalTransport.Helpers.BoundaryLocalization
public import Papers.TbsPrteOptimalTransport.Helpers.BoundaryMixture
public import Papers.TbsPrteOptimalTransport.Helpers.QuantileGridTransfer
public import Papers.TbsPrteOptimalTransport.Helpers.BoundaryRateAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.BoundaryQuantileAssembly
public import Papers.TbsPrteOptimalTransport.Helpers.SelectedGridIntegrability
public import Papers.TbsPrteOptimalTransport.Helpers.SelectedConditionalLaw
/-! TContinuousPrimitiveRate statements. -/
public section
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
namespace Papers.TbsPrteOptimalTransport
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology
universe u v
variable {Ω : Type u} {X Z : Type v} [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Z] [TopologicalSpace X] [TopologicalSpace Z]
  [BorelSpace X] [BorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Z]
variable (M : LatentIVModel Ω X Z)
variable (zeroLaw : X → {ν : ProbabilityMeasure ℝ // ν.toMeasure M.Ysetᶜ = 0})
variable {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
variable (S : ObservedSample M μ)
-- @node: thm:continuous-primitive-rate
/-- Assume [compact Borel domains](hyp:hDomains), [known outcome endpoints](hyp:hEndpoints),
[supported potential outcomes](hyp:hPotential), [consistency](hyp:hConsistency),
[instrument exogeneity](hyp:hExogeneity), [threshold crossing](hyp:hThreshold),
[uniform resistance](hyp:hUniform), [common instrument support](hyp:hSupport),
[finitely many instrument components](hyp:hComponents), [continuous propensity on each component](hyp:hContinuous),
and [a connected instrument domain](hyp:hConnected).
For [an admissible policy](hyp:hPolicy) that [is Lipschitz with the given constant](hyp:hLipschitz), suppose
[split fractions converge to positive proportions](hyp:hSplit), [both grid sizes are positive](hyp:hMG,hMQ),
[unknown endpoints require at least two quantile grid cells](hyp:hInterior), the [bandwidth sequence](hyp:h)
[is positive](hyp:hh), and
[the learners follow the continuous estimation procedure](hyp:hProcedure).
If [the first stage obeys its uniform rate](hyp:hFirstStage), [the outcome learner obeys its local regression rate](hyp:hOutcome),
[trimming satisfies the grid restrictions](hyp:hTrimming), [boundary-grid errors obey their rate](hyp:hGrid),
[the retained clipped grid functions are almost everywhere measurable](hyp:hClippedMeas), and
[all tuning and error sequences vanish](hyp:hVanishes), then
[there exist endpoint, regression, and boundary rates bounded respectively by the first-stage rate, the sum of local regression and first-stage rates, and the sum of quantile-grid, selection-window, first-stage, trimming, and inverse-grid rates, satisfying the corresponding learner bounds with vanishing regression and boundary rates; the interpolated cumulative-quantile plug-in error is bounded in probability at the sum of these primitive rates and the inverse square root of sample size](goal). -/
theorem primitive_learner_rate
    (hDomains : DomainsCompactBorel M) (hEndpoints : OutcomeEndpointsKnown M)
    (hPotential : PotentialSupport M) (hConsistency : Consistency M)
    (hExogeneity : InstrumentExogeneity M) (hThreshold : ThresholdCrossing M)
    (hUniform : UniformResistance M) (hSupport : CommonInstrumentSupport M)
    (hComponents : FiniteInstrumentComponents Z)
    (hContinuous : PropensityContinuousOnComponents M)

    (hConnected : InstrumentConnected Z) (phi : Z → X → ℝ → ℝ) (hPolicy : IsPolicyMap phi)
    (Lphi : ℝ) (hLipschitz : PolicyLipschitz phi Lphi)
    (I : Fin 3 → SampleSplit A) (rho : Fin 3 → ℝ) (hSplit : SplitProportions' μ I rho)
    (pHat : ℕ → A → Z → X → ℝ) (gHat : ℕ → A → ℝ → X → ℝ)
    (raw gGrid beta : ℕ → A → ℕ → X → ℝ)
    (MG MQ : ℕ → ℕ) (hMG : ∀ n, 0 < MG n) (hMQ : ∀ n, 0 < MQ n)
    (knownEndpoints : Bool) (hInterior : knownEndpoints = false → ∀ n, 2 ≤ MQ n)
    (h delta : ℕ → ℝ) (hh : ∀ n, 0 < h n) (K : ℝ → ℝ)
    (Fn : ℕ → Set (X → ℝ)) (FQ : Set (X → ℝ))
    (firstStage : (n : ℕ) → (Finset ℕ × (Fin n → Unit ⊕ Obs X Z)) → Z → X → ℝ)
    (hProcedure : (continuousProcedure M μ S I phi pHat gHat raw gGrid beta
      MG MQ hMG hMQ knownEndpoints hInterior h delta hh K Fn FQ firstStage).1)
    (rp rgloc rQ eps : ℕ → ℝ)
    (hFirstStage : FirstStageUniformRate M μ pHat rp)
    (hOutcome : OutcomeLearnerRate M μ phi pHat gHat rgloc)
    (hTrimming : TrimmingSequence eps MQ)
    (hGrid : BoundaryGridRate M μ zeroLaw pHat delta raw MQ hMQ eps rQ)
    (hClippedMeas : ∀ n, ∀ᵐ a ∂μ, ∀ m ∈ interiorIdx MQ hMQ eps n,
      AEMeasurable (clippedGrid M raw n a m) (xLaw M))
    (hVanishes : TuningVanishes rp rgloc rQ delta eps MQ) :
    let QHat := fun n a x => interpolatedQuantile M raw (MQ n) (hMQ n) knownEndpoints (fun hk => hInterior hk n) n a x
    (∃ re rg rmu : ℕ → ℝ,
      Asymptotics.IsBigO atTop re rp ∧
      Asymptotics.IsBigO atTop rg (fun n => rgloc n + rp n) ∧
      Asymptotics.IsBigO atTop rmu (fun n => rQ n + delta n + rp n + eps n + (MQ n : ℝ)⁻¹) ∧
      EndpointMapRates M μ phi pHat re ∧ RegressionTargetRate M μ phi pHat gHat rg ∧
      RegressionRateVanishes rg ∧ BoundaryLawRate M zeroLaw μ QHat rmu ∧ BoundaryRateVanishes rmu) ∧
    Causalean.Stat.IsBigOp
      (fun n a => |plugInRV M μ S (I 2) phi pHat gHat
        (fun n a x => interpCumQuantile (MQ n) (hMQ n) (QHat n a x)) n a -
        thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))|)
      (fun n => (n : ℝ)^(-1/2 : ℝ) + rp n + rgloc n + rQ n + delta n + eps n + (MQ n : ℝ)⁻¹) μ := by
  have hpRange : ∀ n a z x, pHat n a z x ∈ Icc (0 : ℝ) 1 := by
    intro n a z x
    rw [hProcedure.2.2.2 n a z x]
    exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hpVanishes : Tendsto rp atTop (𝓝 0) := (hVanishes rp (by simp)).2
  have hEndpointRate : EndpointMapRates M μ phi pHat rp :=
    first_stage_endpoint_map_rates M μ phi Lphi hLipschitz pHat hpRange rp
      hFirstStage hpVanishes
  have hStructural : StructuralAssumptions M :=
    ⟨hPotential, hConsistency, hExogeneity, hThreshold, hUniform, hSupport, hDomains⟩
  have hFit := hProcedure.1.2.1
  have hpMeas (n : ℕ) (a : A) : Measurable (Function.uncurry (pHat n a)) := by
    change Measurable (fun zx : Z × X => pHat n a zx.1 zx.2)
    simpa only [Function.comp_def, id_eq] using
      (hFit.2.2.2.2.1 n).comp ((measurable_const (a := a)).prodMk measurable_id)
  have hgMeas (n : ℕ) (a : A) :
      Measurable (fun tx : Icc (0 : ℝ) 1 × X => gHat n a tx.1.val tx.2) := by
    simpa only [Function.comp_def, id_eq] using
      (hFit.2.2.2.2.2.1 n).comp ((measurable_const (a := a)).prodMk measurable_id)
  have hgRange : ∀ n a t x, t ∈ Icc (0 : ℝ) 1 →
      gHat n a t x ∈ Icc (min 0 M.yMin) (max 0 M.yMax) := by
    intro n a t x ht
    rw [hProcedure.1.2.2.2.1 n a t x]
    have horder : min 0 M.yMin ≤ max 0 M.yMax :=
      (min_le_left _ _).trans (le_max_left _ _)
    exact ⟨le_min horder (le_max_left _ _), min_le_left _ _⟩
  have hRegressionRate : RegressionTargetRate M μ phi pHat gHat
      (fun n => rgloc n + rp n) :=
    first_stage_regression_target_rates M μ hStructural hEndpoints phi hPolicy
      Lphi hLipschitz pHat gHat hpMeas hgMeas hpRange hgRange rp rgloc
      hFirstStage hOutcome
  have hRegressionVanishes : RegressionRateVanishes (fun n => rgloc n + rp n) := by
    have hloc := hVanishes rgloc (by simp)
    refine ⟨fun n => add_nonneg (hloc.1 n) (hFirstStage.1 n), ?_⟩
    simpa only [add_zero] using hloc.2.add hpVanishes
  let QHat := fun n a x => interpolatedQuantile M raw (MQ n) (hMQ n)
    knownEndpoints (fun hk => hInterior hk n) n a x
  let rmu := fun n => rQ n + delta n + rp n + eps n + (MQ n : ℝ)⁻¹
  have hQVan := hVanishes rQ (by simp)
  have hdVan := hVanishes delta (by simp)
  have heVan := hVanishes eps (by simp)
  have hMVan := hVanishes (fun n => (MQ n : ℝ)⁻¹) (by simp)
  have hmuNonneg (n : ℕ) : 0 ≤ rmu n := by
    dsimp only [rmu]
    linarith [hQVan.1 n, hdVan.1 n, hFirstStage.1 n, heVan.1 n, hMVan.1 n]
  have hBoundaryVanishes : BoundaryRateVanishes rmu := by
    refine ⟨hmuNonneg, ?_⟩
    simpa only [add_zero] using
      (((hQVan.2.add hdVan.2).add hpVanishes).add heVan.2).add hMVan.2
  have hBoundaryRate : BoundaryLawRate M zeroLaw μ QHat rmu := by
    let grid := fun n a => (MQ n : ℝ)⁻¹ *
      ∑ m ∈ interiorIdx MQ hMQ eps n, ∫ x, pLow M.prop x *
        |clippedGrid M raw n a m x - selQuantile M zeroLaw pHat delta n a x
          (gridLevel (MQ n) (hMQ n) m)| ∂xLaw M
    let B := M.yMax - M.yMin
    have hB : 0 ≤ B := sub_nonneg.mpr (hEndpoints.1.2 hEndpoints.2.1)
    have hEnvelope := primitive_boundary_envelope_rate grid
      (uniformFirstStageError M pHat) rQ rp delta eps
      (fun n => (MQ n : ℝ)⁻¹) B hGrid hFirstStage hdVan.1 heVan.1 hMVan.1
    apply boundedAtRate_of_ae_domination hEnvelope
    intro n
    filter_upwards [hClippedMeas n] with a hClipped
    have hLow (x : X) : 0 ≤ pLow M.prop x :=
      (population_support_endpoints M x).1.1
    have hGridNonneg : 0 ≤ grid n a := by
      apply mul_nonneg (hMVan.1 n)
      apply Finset.sum_nonneg
      intro m hm
      exact integral_nonneg fun x => mul_nonneg (hLow x) (abs_nonneg _)
    have hEnvelopeNonneg : 0 ≤ grid n a +
        B * (delta n + 2 * uniformFirstStageError M pHat n a) +
        2 * B * eps n + 4 * B * (MQ n : ℝ)⁻¹ := by
      have hpNonneg := (uniform_first_stage_error_bounds M pHat hpRange n a).1
      exact add_nonneg (add_nonneg (add_nonneg hGridNonneg
        (mul_nonneg hB (add_nonneg (hdVan.1 n) (mul_nonneg (by norm_num) hpNonneg))))
        (mul_nonneg (mul_nonneg (by norm_num) hB) (heVan.1 n)))
        (mul_nonneg (mul_nonneg (by norm_num) hB) (hMVan.1 n))
    rw [abs_of_nonneg (integral_nonneg fun x =>
      mul_nonneg (hLow x) (integral_nonneg fun _ => abs_nonneg _)),
      abs_of_nonneg hEnvelopeNonneg]
    let err := fun m x => pLow M.prop x *
      |clippedGrid M raw n a m x - selQuantile M zeroLaw pHat delta n a x
        (gridLevel (MQ n) (hMQ n) m)|
    have hSelected :
        (∀ᵐ x ∂xLaw M, pLow M.prop x * quantileDistanceIntegral
          (selLaw M zeroLaw pHat delta n a x) (boundaryLaw M zeroLaw x) ≤
            B * (delta n + 2 * uniformFirstStageError M pHat n a)) ∧
        (∀ m ∈ interiorIdx MQ hMQ eps n, Integrable (err m) (xLaw M)) := by
      constructor
      · have hMixture := selected_boundary_mixture_localization M zeroLaw
          hStructural hEndpoints pHat hpRange delta hdVan.1
        filter_upwards [hMixture,
          conditional_selected_submeasure_evaluation M hStructural,
          conditional_selected_submeasure_mass M hStructural] with x hx hEval hMass
        let D := {z | pHat n a z x ≤ pLow (pHat n a) x + delta n}
        have hD : MeasurableSet D := by
          first | fun_prop | exact (measurableSet_le
            ((hpMeas n a).comp (measurable_id.prodMk measurable_const)) measurable_const)
        let selected := (condDistrib (fun s => (M.Y s, M.W s, M.Zv s))
          M.Xv M.law.toMeasure x).restrict
          {o : ℝ × ℝ × Z | o.2.1 = 1 ∧ o.2.2 ∈ D}
        have hSelectedMass : selected univ =
            ∫⁻ z in D, ENNReal.ofReal (M.prop z x) ∂M.instKernel x := hMass D hD
        by_cases hz : selected univ = 0
        · have hFallback : selLaw M zeroLaw pHat delta n a x = boundaryLaw M zeroLaw x := by
            change (if selected univ = 0 then _ else _) = _
            rw [if_pos hz]
          rw [hFallback]
          simp only [quantileDistanceIntegral, sub_self, abs_zero, integral_zero, mul_zero]
          exact mul_nonneg hB (add_nonneg (hdVan.1 n)
            (mul_nonneg (by norm_num) (uniform_first_stage_error_bounds M pHat hpRange n a).1))
        · have hSelectedEval (C : Set ℝ) (hC : MeasurableSet C) :
              selLaw M zeroLaw pHat delta n a x C = (selected univ)⁻¹ *
                ∫⁻ z in D, canonSubmeasure M true x (M.prop z x) C ∂M.instKernel x := by
            change (if selected univ = 0 then boundaryLaw M zeroLaw x
              else (selected univ)⁻¹ • selected.map Prod.fst) C = _
            rw [if_neg hz, Measure.smul_apply, smul_eq_mul]
            exact congrArg (fun v => (selected univ)⁻¹ * v) (hEval D hD C hC)
          let f := fun z => ENNReal.ofReal (M.prop z x)
          have hp : Measurable (fun z => M.prop z x) := by
            first | fun_prop | exact (hStructural.2.2.2.1.2.1.comp
              (measurable_id.prodMk measurable_const))
          have hf : Measurable f := hp.ennreal_ofReal
          let μz := (∫⁻ z in D, f z ∂M.instKernel x)⁻¹ •
            ((M.instKernel x).restrict D).withDensity f
          have hμz : IsProbabilityMeasure μz := by
            apply normalized_weighted_window_probability
            · change (∫⁻ z in D, ENNReal.ofReal (M.prop z x) ∂M.instKernel x) ≠ 0
              rw [← hSelectedMass]
              exact hz
            · rw [← hSelectedMass]
              exact measure_ne_top selected univ
          obtain ⟨L, hL, hFactor, hRep⟩ := canonical_treated_instrument_kernel M x hp
          have hPosterior : ∀ᵐ z ∂μz, z ∈ D ∧ f z ≠ 0 :=
            normalized_weighted_window_ae (M.instKernel x) D hD f hf
          have hRepAE : ∀ᵐ z ∂μz, L z =
              (ENNReal.ofReal (M.prop z x))⁻¹ •
                canonSubmeasure M true x (M.prop z x) := by
            filter_upwards [hPosterior] with z hz
            exact hRep z (ENNReal.ofReal_ne_zero_iff.mp hz.2)
          have hWindow : ∀ᵐ z ∂μz,
              pHat n a z x ≤ pLow (pHat n a) x + delta n :=
            hPosterior.mono fun z hz => hz.1
          have hLaw : selLaw M zeroLaw pHat delta n a x = μz.bind L := by
            apply Measure.ext
            intro C hC
            rw [hSelectedEval C hC, hSelectedMass,
              Measure.bind_apply hC L.measurable.aemeasurable,
              normalized_weighted_window_lintegral (M.instKernel x) D f
                (fun z => L z C) hf (L.measurable_coe hC)]
            congr 1
            apply lintegral_congr
            intro z
            simpa only [Measure.smul_apply, smul_eq_mul] using
              (congrArg (fun ν : Measure ℝ => ν C) (hFactor z)).symm
          rw [hLaw]
          exact hx n a μz hμz L hL hRepAE hWindow
      · intro m hm
        have hm' := Finset.mem_filter.mp hm
        have hidx := Finset.mem_Icc.mp hm'.1
        have hNr : (0 : ℝ) < MQ n := by exact_mod_cast hMQ n
        have ht : gridLevel (MQ n) (hMQ n) m ∈ Ioo (0 : ℝ) 1 := by
          constructor
          · exact div_pos (by exact_mod_cast (show 0 < m by omega)) hNr
          · exact (div_lt_one hNr).mpr
              (by exact_mod_cast (show m < MQ n by omega))
        exact selected_grid_error_integrable M zeroLaw hStructural hEndpoints pHat
          (fun n => hFit.2.2.2.2.1 n) hpRange delta raw n a m
          (gridLevel (MQ n) (hMQ n) m) ht (hClipped m hm)
    have hTriangle := interpolated_boundary_error_via_selected M zeroLaw
      hStructural hEndpoints pHat delta (fun n => hFit.2.2.2.2.1 n)
      raw MQ hMQ eps (fun n => (inv_nonneg.mpr (Nat.cast_nonneg (MQ n))).trans
        (hTrimming.1 n).1) knownEndpoints hInterior n a
      (hFit.2.2.2.2.2.2.2.2.1 n a)
    have : IsProbabilityMeasure (xLaw M) :=
      Measure.isProbabilityMeasure_map M.measX.aemeasurable
    apply boundary_grid_envelope_integral (xLaw M) (interiorIdx MQ hMQ eps n)
      (fun x => pLow M.prop x * quantileDistanceIntegral
        (boundaryLawHat QHat n a x) (boundaryLaw M zeroLaw x)) err
      (MQ n : ℝ)⁻¹ (B * (delta n + 2 * uniformFirstStageError M pHat n a))
      (2 * B * eps n) (4 * B * (MQ n : ℝ)⁻¹)
      (fun x => mul_nonneg (hLow x) (integral_nonneg fun _ => abs_nonneg _))
      hSelected.2
    filter_upwards [hTriangle, hSelected.1] with x ht hs
    have ht' := ht.trans (add_le_add le_rfl hs)
    dsimp only [err, QHat, B] at *
    rw [← Finset.mul_sum]
    nlinarith [ht']
  constructor
  · exact ⟨rp, (fun n => rgloc n + rp n), rmu,
      Asymptotics.isBigO_refl _ _, Asymptotics.isBigO_refl _ _,
      Asymptotics.isBigO_refl _ _, hEndpointRate, hRegressionRate,
      hRegressionVanishes, hBoundaryRate, hBoundaryVanishes⟩
  · let r := fun n : ℕ => (n : ℝ)^(-1/2 : ℝ) + rp n + rgloc n +
        rQ n + delta n + eps n + (MQ n : ℝ)⁻¹
    have hrp (n : ℕ) := hFirstStage.1 n
    have hrg (n : ℕ) := hRegressionVanishes.1 n
    have hgl (n : ℕ) := (hVanishes rgloc (by simp)).1 n
    have hrNonneg (n : ℕ) : 0 ≤ r n := by
      dsimp only [r]
      linarith [Real.rpow_nonneg (Nat.cast_nonneg n) (-1/2 : ℝ),
        hrp n, hgl n, hQVan.1 n, hdVan.1 n, heVan.1 n, hMVan.1 n]
    have hrPos : ∀ᶠ n in atTop, 0 < r n := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hroot := Real.rpow_pos_of_pos hnp (-1/2 : ℝ)
      dsimp only [r]
      linarith [hrp n, hgl n, hQVan.1 n, hdVan.1 n, heVan.1 n, hMVan.1 n]
    have hbase := plugin_rate M zeroLaw μ S hDomains hEndpoints hPotential hConsistency
      hExogeneity hThreshold hUniform hSupport hComponents hContinuous hConnected
      phi hPolicy I rho pHat gHat QHat
      (ConnectedFitScope.toJoint M μ S I pHat gHat QHat hFit) hSplit rp (fun n => rgloc n + rp n) rmu
      hEndpointRate hRegressionRate hRegressionVanishes hBoundaryRate hBoundaryVanishes
    have hbaseRate : Causalean.Stat.IsBigOp
        (fun n a => |plugInRV M μ S (I 2) phi pHat gHat
          (fun n a x => quantilePrimitive (QHat n a x)) n a -
          thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))|) r μ := by
      apply Causalean.Stat.IsBigOp.scale_rate (c := 3) (by norm_num)
      apply Causalean.Stat.IsBigOp.mono_rate (h := hbase)
      intro n
      dsimp only [r, rmu]
      linarith [Real.rpow_nonneg (Nat.cast_nonneg n) (-1/2 : ℝ),
        hrp n, hgl n, hQVan.1 n, hdVan.1 n, heVan.1 n, hMVan.1 n]
    let E := fun n a => plugInRV M μ S (I 2) phi pHat gHat
      (fun n a x => interpCumQuantile (MQ n) (hMQ n) (QHat n a x)) n a -
      plugInRV M μ S (I 2) phi pHat gHat
        (fun n a x => quantilePrimitive (QHat n a x)) n a
    have hB : 0 ≤ M.yMax - M.yMin := sub_nonneg.mpr (hEndpoints.1.2 hEndpoints.2.1)
    have hEbound (n : ℕ) (a : A) : |E n a| ≤ 2 * (M.yMax - M.yMin) * r n := by
      have he : 0 ≤ (M.yMax - M.yMin) / (MQ n : ℝ) := by positivity
      have hdiff := plugin_lower_cumulative_perturbation M μ S (I 2) phi hPolicy
        pHat hpRange gHat
        (fun n a x => interpCumQuantile (MQ n) (hMQ n) (QHat n a x))
        (fun n a x => quantilePrimitive (QHat n a x)) n a
        ((M.yMax - M.yMin) / (MQ n : ℝ)) he
        (fun x t ht => interpolated_quantile_cumulative_error M hEndpoints raw
          (MQ n) (hMQ n) knownEndpoints (fun hk => hInterior hk n) n a x t ht)
      have hmr : (MQ n : ℝ)⁻¹ ≤ r n := by
        dsimp only [r]
        linarith [Real.rpow_nonneg (Nat.cast_nonneg n) (-1/2 : ℝ),
          hrp n, hgl n, hQVan.1 n, hdVan.1 n, heVan.1 n]
      exact hdiff.trans (by
        rw [div_eq_mul_inv, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left hmr (by positivity))
    have hE := isBigOp_of_uniform_rate_bound (μ := μ) (2 * (M.yMax - M.yMin))
      (by positivity) hrPos hEbound
    have hEabs : Causalean.Stat.IsBigOp (fun n a => |E n a|) r μ :=
      Causalean.Stat.IsBigOp.of_abs_le (fun n a => by rw [abs_abs]) hE
    apply Causalean.Stat.IsBigOp.of_abs_le _ (hEabs.add hbaseRate)
    intro n a
    simp only [abs_abs]
    rw [abs_of_nonneg (add_nonneg (abs_nonneg (E n a))
      (abs_nonneg (plugInRV M μ S (I 2) phi pHat gHat
        (fun n a x => quantilePrimitive (QHat n a x)) n a -
        thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop)))))]
    calc
      _ ≤ |E n a| + |plugInRV M μ S (I 2) phi pHat gHat
          (fun n a x => quantilePrimitive (QHat n a x)) n a -
          thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))| := by
        convert abs_add_le (E n a) (plugInRV M μ S (I 2) phi pHat gHat
          (fun n a x => quantilePrimitive (QHat n a x)) n a -
          thetaLower1 (transportData M) (policyWeight M (policyProp phi M.prop))) using 1
        all_goals first | rfl | (dsimp only [E, QHat]; congr 1; ring)

end Papers.TbsPrteOptimalTransport
