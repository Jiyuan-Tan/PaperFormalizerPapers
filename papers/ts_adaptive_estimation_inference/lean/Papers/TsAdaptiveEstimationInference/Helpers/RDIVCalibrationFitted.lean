module
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVSelectedOperatorTransport
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVCalibrationEvent
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVCalibrationTransfer
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVAcceptance
/-! Bernstein concentration for the actual training-measurable calibration residual. -/
public section
set_option linter.style.setOption false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option maxHeartbeats 800000
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory ProbabilityTheory Filter
variable {𝒲 X Z Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace X]
  [MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
  {pilotInputSupport : Set Z}
  (V : IVWorld 𝒲 X Z) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

/-- If [q is measurable](hyp:hq), [B is nonnegative](hyp:hB), [q is bounded in
absolute value by 2B almost everywhere under the observation law](hyp:hbound),
[the calibration sample size n is positive](hyp:hn), and [ζ lies strictly
between zero and one](hyp:hζ), [with probability at least 1 − ζ the calibration
average of q squared differs from its population mean by at most
(4B + 8B² + 3) times the sum of the input L2 norm of q times
√(log(2/ζ)/n) and log(2/ζ)/n](goal). -/
-- @node: rdiv_frozen_calibration_block_bernstein
lemma rdiv_frozen_calibration_block_bernstein
    (q : 𝒲 → ℝ) (B : ℝ) (hq : Measurable q) (hB : 0 ≤ B)
    (hbound : ∀ᵐ w ∂V.law, |q w| ≤ 2 * B)
    (n : ℕ) (hn : 0 < n) (ζ : ℝ) (hζ : ζ ∈ Set.Ioo (0 : ℝ) 1) :
    1 - ζ ≤ P.real {ω |
      |blockAverage V P sample (split.cal n) (fun w => q w ^ 2) ω -
          inputL2Norm V.law q ^ 2| ≤
        (4 * B + 8 * B ^ 2 + 3) *
          (Real.sqrt (Real.log (2 / ζ) / n) * inputL2Norm V.law q +
            Real.sqrt (Real.log (2 / ζ) / n) ^ 2)} := by
  classical
  obtain ⟨E, _, hpE, hgood⟩ := rdiv_frozen_calibration_bernstein sample q B hq hB
    hbound n hn ζ hζ
  let first : Ω → Fin n → 𝒲 := fun ω i => sample.Z i ω
  let cal : Ω → Fin n → 𝒲 := fun ω i =>
    sample.Z ((Finset.equivFinOfCardEq (split.card_cal n)).symm i) ω
  have hfirst : Measurable first := measurable_pi_lambda _ fun i => sample.meas i
  have hcal : Measurable cal := measurable_pi_lambda _ fun i => sample.meas _
  have hfirstLaw : P.map first = Measure.pi (fun _ : Fin n => V.law) := by
    have hi := sample.indep.precomp (Fin.val_injective (n := n))
    have he := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => (sample.meas i).aemeasurable)).mp hi
    change P.map first = _ at he
    rw [he]
    simp_rw [sample.map_eq]
  have hcalLaw : P.map cal = Measure.pi (fun _ : Fin n => V.law) := by
    have hinj : Function.Injective (fun i : Fin n =>
        ((Finset.equivFinOfCardEq (split.card_cal n)).symm i : ℕ)) :=
      Subtype.val_injective.comp (Equiv.injective _)
    have hi := sample.indep.precomp hinj
    have he := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => (sample.meas _).aemeasurable)).mp hi
    change P.map cal = _ at he
    rw [he]
    simp_rw [sample.map_eq]
  let T : Set (Fin n → 𝒲) := {v |
    |(n : ℝ)⁻¹ * ∑ i, q (v i) ^ 2 - inputL2Norm V.law q ^ 2| ≤
      (4 * B + 8 * B ^ 2 + 3) *
        (Real.sqrt (Real.log (2 / ζ) / n) * inputL2Norm V.law q +
          Real.sqrt (Real.log (2 / ζ) / n) ^ 2)}
  have hT : MeasurableSet T := by
    apply measurableSet_le _ measurable_const
    fun_prop
  have hp : 1 - ζ ≤ P.real (first ⁻¹' T) := hpE.trans (measureReal_mono (by
    intro ω hω
    have he := hgood ω hω
    simpa only [T, first, Set.mem_preimage, Set.mem_setOf_eq,
      Causalean.Stat.IIDSample.sampleMean, ← Fin.sum_univ_eq_sum_range] using he))
  have heq : P (cal ⁻¹' T) = P (first ⁻¹' T) := by
    rw [← Measure.map_apply hcal hT, ← Measure.map_apply hfirst hT,
      hcalLaw, hfirstLaw]
  have hsets : cal ⁻¹' T = {ω |
      |blockAverage V P sample (split.cal n) (fun w => q w ^ 2) ω -
          inputL2Norm V.law q ^ 2| ≤
        (4 * B + 8 * B ^ 2 + 3) *
          (Real.sqrt (Real.log (2 / ζ) / n) * inputL2Norm V.law q +
            Real.sqrt (Real.log (2 / ζ) / n) ^ 2)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, T, cal]
    rw [rdiv_calibration_tuple_average V P sample split n (fun w => q w ^ 2) ω]
  rw [← hsets]
  change 1 - ζ ≤ (P (cal ⁻¹' T)).toReal
  rw [heq]
  exact hp

/-- If [the sample size is positive](hyp:hn), [B is nonnegative](hyp:hB),
[ξ lies strictly between zero and one](hyp:hξ), [each grid residual is jointly
measurable in the preliminary-and-fitting information and a fresh observation](hyp:hq),
and [each residual is bounded in absolute value by 2B for almost every training
outcome and fresh observation](hyp:hbound), [there is a measurable event of
probability at least 1 − ξ/4 on which, simultaneously over the grid, calibration
residual energy differs from population residual energy by at most
(4B + 8B² + 3) times the sum of the residual norm times the quarter-grid logarithmic
radius and that radius squared](goal). -/
-- @node: rdiv_calibration_bernstein_event
lemma rdiv_calibration_bernstein_event
    (n : ℕ) (hn : 0 < n) (ρ ξ B : ℝ) (hB : 0 ≤ B)
    (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (q : ℝ → Ω → 𝒲 → ℝ)
    (hq : ∀ lam ∈ regGrid ρ n,
      @Measurable (Ω × 𝒲) ℝ
        ((⨆ i ∈ split.pre n ∪ split.fit n,
          MeasurableSpace.comap (sample.Z i) inferInstance).prod inferInstance)
        inferInstance (fun p => q lam p.1 p.2))
    (hbound : ∀ lam ∈ regGrid ρ n, ∀ᵐ training ∂P,
      ∀ᵐ w ∂V.law, |q lam training w| ≤ 2 * B) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 4 ≤ P.real E ∧
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        |blockAverage V P sample (split.cal n) (fun w => q lam ω w ^ 2) ω -
          inputL2Norm V.law (q lam ω) ^ 2| ≤
            (4 * B + 8 * B ^ 2 + 3) *
              (Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n) *
                inputL2Norm V.law (q lam ω) +
                Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n) ^ 2) := by
  have hη : gridConfidence ρ ξ n / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    have hk : (1 : ℝ) ≤ (terminalIndex ρ n + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hηle : gridConfidence ρ ξ n ≤ ξ := by
      unfold gridConfidence
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith only [hk, hξ.1])
    constructor
    · have hx := hξ.1
      unfold gridConfidence
      positivity
    · linarith only [hηle, hξ.2]
  obtain ⟨E, hE, hpE, hgood⟩ :=
    rdiv_calibration_bernstein_event_of_frozen_bounds V P sample split n ρ ξ
      (4 * B + 8 * B ^ 2 + 3)
      (Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n)) hξ q hq (by
        intro lam hlam
        filter_upwards [hbound lam hlam] with training ht
        have hm : Measurable (q lam training) := (hq lam hlam).of_uncurry_left
        have hb := rdiv_frozen_calibration_block_bernstein V P sample split
          (q lam training) B hm hB ht n hn _ hη
        simpa only [inputL2Norm, Real.sq_sqrt (integral_nonneg
          (fun w => sq_nonneg (q lam training w)))] using hb)
  refine ⟨E, hE, hpE, ?_⟩
  intro ω hω lam hlam
  simpa only [inputL2Norm, Real.sq_sqrt (integral_nonneg
    (fun w => sq_nonneg (q lam ω w)))] using hgood ω hω lam hlam

/-- If [the grid ratio is at least one half and less than one](hyp:hρ),
[ξ lies strictly between zero and one](hyp:hξ), and [the sample size is
positive](hyp:hn), [the square root of log of two divided by the quarter-grid
failure probability, divided by the sample size, is at most twice the public
logarithmic scale](goal). -/
-- @node: rdiv_calibration_log_radius_le
lemma rdiv_calibration_log_radius_le (ρ ξ : ℝ)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (n : ℕ) (hn : 0 < n) :
    Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n) ≤
      2 * rdivPublicLogScale ρ ξ n := by
  have hk : (2 : ℝ) ≤ ((terminalIndex ρ n : ℝ) + 1) := by
    exact_mod_cast (show 2 ≤ terminalIndex ρ n + 1 by
      have := rdiv_terminalIndex_pos ρ hρ n hn
      omega)
  have hr : (2 : ℝ) ≤ ((terminalIndex ρ n : ℝ) + 1) / ξ := by
    apply (le_div_iff₀ hξ.1).2
    linarith [hξ.2]
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hr
  have hlog0 : 0 ≤ Real.log (((terminalIndex ρ n : ℝ) + 1) / ξ) :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hl
  have heq : 2 / (gridConfidence ρ ξ n / 4) =
      (((terminalIndex ρ n : ℝ) + 1) / ξ) * 2 ^ 3 := by
    unfold gridConfidence
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, Nat.cast_add, Nat.cast_one]
    ring
  have hlog : Real.log (2 / (gridConfidence ρ ξ n / 4)) ≤
      4 * Real.log (((terminalIndex ρ n : ℝ) + 1) / ξ) := by
    rw [heq, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hl]
  unfold rdivPublicLogScale
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (div_nonneg hlog0 (Nat.cast_nonneg n))]
  simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc, show (2 : ℝ) ^ 2 = 4 by norm_num] using
    div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)

/-- Assume [the RDIV model conditions hold](hyp:hIV), [the density class is
realizable](hyp:hDensity), [the common support and density bounds hold](hyp:hBounds),
[the hypothesis class is bounded by B on the support](hyp:hHyp), [the RDIV
classes satisfy the required measurability conditions](hyp:hSupMeas), [the
candidates attain the empirical minima](hyp:hMinima), [the fitted density is
a selected maximum-likelihood maximizer](hyp:hMLE), and [the selected density
has a coherent preliminary-measurable version](hyp:hSelectedDensityVersion).
For [a positive sample size](hyp:hn), [there is an operator version jointly
measurable in the preliminary-and-fitting information and input at each grid
penalty, together with a measurable probability-one set on which this version
agrees with the selected estimated operator both almost everywhere under the
input law and at every calibration observation, simultaneously over the grid](goal). -/
-- @node: rdiv_selected_operator_calibration_version
lemma rdiv_selected_operator_calibration_version
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (support : Set (X × Z))
    (B c₀ CG ρ : ℝ) (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hIV : RDIVSetting V μ g₀)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B)
    (hSupMeas : RDIVClassesMeasurable V P sample split μ G g₀ gHat)
    (hMinima : RDIVMinimaAttained V P sample split μ gHat ρ candidate)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split μ gHat)
    (n : ℕ) (hn : 0 < n) :
    ∃ op : ℝ → Ω → Z → ℝ,
      (∀ lam ∈ regGrid ρ n, @Measurable (Ω × Z) ℝ
        ((⨆ i ∈ split.pre n ∪ split.fit n,
          MeasurableSpace.comap (sample.Z i) inferInstance).prod inferInstance)
        inferInstance (fun p => op lam p.1 p.2)) ∧
      ∃ N : Set Ω, MeasurableSet N ∧ (∀ᵐ ω ∂P, ω ∈ N) ∧
        ∀ ω ∈ N, ∀ lam ∈ regGrid ρ n,
          (op lam ω =ᵐ[V.law.map V.zOf]
            estimatedOperator V μ gHat n ω (candidate n lam ω)) ∧
          (∀ i ∈ split.cal n, op lam ω (V.zOf (sample.Z i ω)) =
            estimatedOperator V μ gHat n ω (candidate n lam ω)
              (V.zOf (sample.Z i ω))) := by
  exact rdiv_selected_family_operator_calibration_version V P sample split
    μ G g₀ gHat support B c₀ CG ρ (candidate n) hIV hDensity hBounds hHyp
    hMLE hSelectedDensityVersion n hn
    (fun lam hlam ω => ((hMinima n hn lam hlam).1 ω).1)
    (fun lam hlam => (hMinima n hn lam hlam).2)


/-- Assume [the RDIV model conditions hold](hyp:hIV), [the density class is
realizable](hyp:hDensity), [the common support and density bounds hold](hyp:hBounds),
[the hypothesis class is bounded by B on the support](hyp:hHyp), [B is
nonnegative](hyp:hB), [the pilot satisfies its regression rate](hyp:_hPilot),
[the pilot is bounded by B on the pilot input support](hyp:hPilotBound), [the
RDIV classes satisfy the required measurability conditions](hyp:hSupMeas),
[the candidates attain the empirical minima](hyp:hMinima), [the fitted density
is a selected maximum-likelihood maximizer](hyp:hMLE), [the selected density
has a coherent preliminary-measurable version](hyp:hSelectedDensityVersion),
and [the selected pilot has a coherent preliminary-measurable version](hyp:hSelectedPilotVersion).
If [ξ lies strictly between zero and one](hyp:hξ) and [the sample size is
positive](hyp:hn), [there is a measurable event of probability at least 1 − ξ/4
on which, simultaneously over grid penalties, the calibration statistic of
the selected candidate differs from its population fitted-residual energy by
at most (4B + 8B² + 3) times the sum of the fitted-residual norm times the
quarter-grid logarithmic radius and that radius squared](goal). -/
-- @node: rdiv_fitted_calibration_bernstein_event
lemma rdiv_fitted_calibration_bernstein_event
    (μ : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG ρ ξ : ℝ) (δr : ℕ → ℝ → ℝ)
    (candidate : ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hIV : RDIVSetting V μ g₀)
    (hDensity : DensityRealizable V μ G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (_hPilot : PilotRegressionRate V P sample split rHat δr)
    (hPilotBound : PilotBounded V P rHat pilotInputSupport B)
    (hSupMeas : RDIVClassesMeasurable V P sample split μ G g₀ gHat)
    (hMinima : RDIVMinimaAttained V P sample split μ gHat ρ candidate)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split μ gHat)
    (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat)
    (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) (hn : 0 < n) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - ξ / 4 ≤ P.real E ∧
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        |rdivCalibrationStat V P sample split μ gHat rHat n ω (candidate n lam ω) -
          inputL2Norm (V.law.map V.zOf)
            (rHat n ω - estimatedOperator V μ gHat n ω (candidate n lam ω)) ^ 2| ≤
          (4 * B + 8 * B ^ 2 + 3) *
            (Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n) *
              inputL2Norm (V.law.map V.zOf)
                (rHat n ω - estimatedOperator V μ gHat n ω (candidate n lam ω)) +
                Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n) ^ 2) := by
  obtain ⟨op, hop, N, hN, hNae, hidentify⟩ :=
    rdiv_selected_operator_calibration_version (hSelectedDensityVersion := hSelectedDensityVersion) V P sample split μ G g₀ gHat
      support B c₀ CG ρ candidate hIV hDensity hBounds hHyp hSupMeas hMinima hMLE n hn
  obtain ⟨rBar, hrBar, R, hR, hRae, hrcoh⟩ :=
    rdiv_pilot_calibration_version V P sample split rHat B hSelectedPilotVersion hPilotBound n hn
  let q : ℝ → Ω → 𝒲 → ℝ := fun lam ω w =>
    rBar (ω, V.zOf w) - op lam ω (V.zOf w)
  have hq (lam : ℝ) (hlam : lam ∈ regGrid ρ n) :
      @Measurable (Ω × 𝒲) ℝ
        ((⨆ i ∈ split.pre n ∪ split.fit n,
          MeasurableSpace.comap (sample.Z i) inferInstance).prod inferInstance)
        inferInstance (fun p => q lam p.1 p.2) := by
    let mt := ⨆ i ∈ split.pre n ∪ split.fit n,
      MeasurableSpace.comap (sample.Z i) inferInstance
    letI : MeasurableSpace Ω := mΩ
    have hpre : preliminarySigma V P sample split n ≤ mt := by
      apply iSup_le
      intro i
      apply iSup_le
      intro hi
      exact le_iSup_of_le i (le_iSup_of_le (Finset.mem_union_left _ hi) le_rfl)
    letI : MeasurableSpace Ω := mt
    have hp : Measurable (fun p : Ω × Z => rBar (p.1, p.2)) :=
      hrBar.comp
        ((measurable_fst.mono le_rfl hpre).prodMk measurable_snd)
    exact (hp.sub (hop lam hlam)).comp
      (measurable_fst.prodMk (V.measurable_z.comp measurable_snd))
  have hbound (lam : ℝ) (hlam : lam ∈ regGrid ρ n) :
      ∀ᵐ ω ∂P, ∀ᵐ w ∂V.law, |q lam ω w| ≤ 2 * B := by
    filter_upwards [(hMLE n hn).1, hRae, hNae] with ω hg hωR hωN
    have hb := rdiv_hypothesis_density_operator_bounded V μ G g₀ (gHat n ω)
      support B c₀ CG hDensity hBounds hHyp hB hg.1
    have hz : ∀ᵐ z ∂V.law.map V.zOf,
        |rBar (ω, z) - op lam ω z| ≤ 2 * B := by
      filter_upwards [(hrcoh ω hωR).2.1, hb, (hidentify ω hωN lam hlam).1] with z hrz hTz heq
      rw [heq]
      exact (abs_sub _ _).trans (by
        have hT := hTz (candidate n lam ω) ((hMinima n hn lam hlam).1 ω).1
        change |estimatedOperator V μ gHat n ω (candidate n lam ω) z| ≤ B at hT
        linarith only [hrz, hT])
    exact ae_of_ae_map V.measurable_z.aemeasurable hz
  obtain ⟨E, hE, hpE, he⟩ := rdiv_calibration_bernstein_event V P sample split
    n hn ρ ξ B hB hξ q hq hbound
  have hfull : ∀ᵐ ω ∂P, ω ∈ N ∩ R := hNae.and hRae
  have hprob : P.real (E ∩ (N ∩ R)) = P.real E := by
    change (P (E ∩ (N ∩ R))).toReal = (P E).toReal
    rw [Set.inter_comm E (N ∩ R), Measure.measure_inter_eq_of_ae hfull]
  refine ⟨E ∩ (N ∩ R), hE.inter (hN.inter hR), hprob.symm ▸ hpE, ?_⟩
  intro ω hω lam hlam
  have hnorm : inputL2Norm V.law (q lam ω) =
      inputL2Norm (V.law.map V.zOf)
        (rHat n ω - estimatedOperator V μ gHat n ω (candidate n lam ω)) := by
    unfold inputL2Norm
    congr 1
    have hp : Measurable (fun z => rBar (ω, z)) :=
      hrBar.comp (measurable_const.prodMk measurable_id)
    have hT : Measurable (op lam ω) := (hop lam hlam).of_uncurry_left
    calc
      (∫ w, q lam ω w ^ 2 ∂V.law) =
          ∫ z, (rBar (ω, z) - op lam ω z) ^ 2 ∂V.law.map V.zOf :=
        (integral_map V.measurable_z.aemeasurable
          ((hp.sub hT).pow_const 2).aestronglyMeasurable).symm
      _ = _ := integral_congr_ae (by
        filter_upwards [(hidentify ω hω.2.1 lam hlam).1, (hrcoh ω hω.2.2).1] with z hz hrz
        simp only [hz, hrz, Pi.sub_apply])
  have hstat : blockAverage V P sample (split.cal n)
      (fun w => q lam ω w ^ 2) ω =
      rdivCalibrationStat V P sample split μ gHat rHat n ω (candidate n lam ω) := by
    unfold blockAverage rdivCalibrationStat
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [q, (hidentify ω hω.2.1 lam hlam).2 i hi, (hrcoh ω hω.2.2).2.2 i hi]
  have hb := he ω hω.1 lam hlam
  rw [hnorm, hstat] at hb
  exact hb

end Papers.TsAdaptiveEstimationInference
