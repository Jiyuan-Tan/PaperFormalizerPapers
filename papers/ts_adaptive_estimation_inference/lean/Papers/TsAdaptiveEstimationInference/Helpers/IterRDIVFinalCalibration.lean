module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIVCalibration
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVCalibrationFitted
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVOperatorRestriction
/-! Final calibration on the recursive RDIV fitting event.

The Bernstein event is constructed at its prescribed quarter-grid allocation.
Coherent residual versions cost only a null set, and the fitting/pilot event is
retained as a subset. The versions for training-measurable fitted candidates
are constructed locally without changing their representatives or objectives.
-/
public section

namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory
variable {W X Z Ω : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Z] [mΩ : MeasurableSpace Ω]

/-- If [the grid ratio lies in $[1/2,1)$](hyp:hρ), [the failure probability lies
between zero and one](hyp:hξ), [the sample size is positive](hyp:hn), [the base
scales obey the prescribed calibration](hyp:hScale), [the public scales satisfy
the calibrated inflation bounds](hyp:hInflation), and [the quarter-confidence
density radius](hyp:hG) and [pilot radius](hyp:hR) are nonnegative, then [the
Bernstein radius, obtained by dividing the logarithm of two over the quarter-grid
confidence allocation by sample size and taking its square root, is at most
twice the nuisance scale](goal).

The nuisance calibration contains the quarter-grid Bernstein radius after
the existing deterministic inflation. Only the actual quarter-confidence curve
values occur; no monotonicity in the confidence argument is used. -/
-- @node: iter_rdiv_calibration_radius_of_scales
lemma iter_rdiv_calibration_radius_of_scales
    (ρ ξ : ℝ) (t n : ℕ) (δ ν baseδ baseν : ℕ → ℝ)
    (rawG rawH rawR : ℕ → ℝ → ℝ) (κδ κν required : ℝ)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) (hn : 0 < n)
    (hScale : RDIVScaleCalibration ρ ξ baseδ baseν rawG rawH rawR t)
    (hInflation : CalibratedValidBounds δ ν baseδ baseν κδ κν required)
    (hG : 0 ≤ rawG n (ξ / 4)) (hR : 0 ≤ rawR n (ξ / 4)) :
    Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n) ≤ 2 * ν n := by
  have hs := (hScale.2.1 n hn).2
  change rawG n (ξ / 4) + rawR n (ξ / 4) +
    rdivPublicLogScale ρ ξ n ≤ baseν n at hs
  have hlog : rdivPublicLogScale ρ ξ n ≤ baseν n := by
    linarith only [hs, hG, hR]
  have hb : 0 ≤ baseν n := (Real.sqrt_nonneg _).trans hlog
  have hν : baseν n ≤ ν n := by
    rw [hInflation.2.2.2.2.2 n]
    exact le_mul_of_one_le_left hb hInflation.2.1
  exact (rdiv_calibration_log_radius_le ρ ξ hρ hξ n hn).trans
    (mul_le_mul_of_nonneg_left (hlog.trans hν) (by norm_num))

/-- Under [the RDIV model](hyp:hIV), [the range condition](hyp:hRange),
[density realizability](hyp:hDensity), [density bounds](hyp:hBounds), [the
hypothesis envelope B](hyp:hHyp), and [nonnegative B](hyp:hB), assume [a failure
probability between zero and one](hyp:hξ), [positive sample size](hyp:hn), and
[a quarter-grid Bernstein radius at most twice the nuisance scale](hyp:hRadius).
Suppose [the fitting event is measurable](hyp:hF), [has probability at least one
minus three quarters of the failure probability](hyp:hpF), and [on it the
density and candidates are class-valued, the pilot is square-integrable, and
pilot and candidate operator errors are at most the nuisance scale](hyp:hFit).
For [a family of residual functions](hyp:q) that [is jointly measurable from
training data and a fresh observation](hyp:hq), [is almost surely bounded by
2 B on fresh sections](hyp:hbound), and [has the actual residual population
norm and calibration-block squared average](hyp:hidentify), [there is a
measurable subset of the fitting event with probability at least one minus the
failure probability where, uniformly on the penalty grid, calibration error
relative to projected squared error is at most C times nuisance scale times
projected error plus C times squared nuisance scale, with
C = 16(4 B + 8 B² + 3) + 9](goal).

Intersect the actual Bernstein event with the already constructed recursive
fitting/pilot event. The version inputs are only population and actual-block
identities. Bernstein and the projected-error comparison are proved here, with
the remaining quarter of the confidence budget and one unchanged subset event.
The comparison constant depends only on the fixed envelope B. -/
-- @node: iter_rdiv_calibration_event_of_versions
lemma iter_rdiv_calibration_event_of_versions
    (V : IVWorld W X Z) (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG ρ ξ ν : ℝ)
    (n : ℕ) (candidate : ℝ → Ω → V.Hbar.toSubmodule)
    (hIV : RDIVSetting V mu g₀) (hRange : RangeCondition V)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) (hn : 0 < n)
    (hRadius : Real.sqrt (Real.log (2 / (gridConfidence ρ ξ n / 4)) / n) ≤ 2 * ν)
    (F : Set Ω) (hF : MeasurableSet F) (hpF : 1 - 3 * ξ / 4 ≤ P.real F)
    (hFit : ∀ ω ∈ F, gHat n ω ∈ G ∧
      MemLp (rHat n ω) 2 (V.law.map V.zOf) ∧
      inputL2Norm (V.law.map V.zOf)
        (rHat n ω - dualVersion V (momentRepresenter V)) ≤ ν ∧
      ∀ lam ∈ regGrid ρ n, candidate lam ω ∈ V.H ∧
        inputL2Norm (V.law.map V.zOf)
          (estimatedOperator V mu gHat n ω (candidate lam ω) -
            dualVersion V (projCondExpOp V (candidate lam ω))) ≤ ν)
    (q : ℝ → Ω → W → ℝ)
    (hq : ∀ lam ∈ regGrid ρ n, @Measurable (Ω × W) ℝ
      ((⨆ i ∈ split.pre n ∪ split.fit n,
        MeasurableSpace.comap (sample.Z i) inferInstance).prod inferInstance)
      inferInstance (fun p => q lam p.1 p.2))
    (hbound : ∀ lam ∈ regGrid ρ n, ∀ᵐ training ∂P,
      ∀ᵐ w ∂V.law, |q lam training w| ≤ 2 * B)
    (hidentify : ∀ᵐ ω ∂P, ∀ lam ∈ regGrid ρ n,
      inputL2Norm V.law (q lam ω) =
        inputL2Norm (V.law.map V.zOf)
          (rHat n ω - estimatedOperator V mu gHat n ω (candidate lam ω)) ∧
      blockAverage V P sample (split.cal n) (fun w => q lam ω w ^ 2) ω =
        rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate lam ω)) :
    ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ F ∧ 1 - ξ ≤ P.real E ∧
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        |rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate lam ω) -
          ‖projCondExpOp V (candidate lam ω - minNormSolution V)‖ ^ 2| ≤
          (16 * (4 * B + 8 * B ^ 2 + 3) + 9) * ν *
            ‖projCondExpOp V (candidate lam ω - minNormSolution V)‖ +
          (16 * (4 * B + 8 * B ^ 2 + 3) + 9) * ν ^ 2 := by
  obtain ⟨R, hR, hpR, hBernstein⟩ := rdiv_calibration_bernstein_event V P sample split
    n hn ρ ξ B hB hξ q hq hbound
  obtain ⟨N, hsub, hN, hNzero⟩ := exists_measurable_superset_of_null
    (ae_iff.mp hidentify)
  have hpFR : 1 - ξ ≤ P.real (F ∩ R) := by
    have hbad : P.real (F ∩ R)ᶜ ≤ P.real Fᶜ + P.real Rᶜ := by
      rw [Set.compl_inter]
      exact measureReal_union_le _ _
    linarith only [hbad, hpF, hpR, probReal_add_probReal_compl (μ := P) hF,
      probReal_add_probReal_compl (μ := P) hR,
      probReal_add_probReal_compl (μ := P) (hF.inter hR)]
  refine ⟨(F ∩ R) \ N, (hF.inter hR).diff hN,
    fun ω hω => hω.1.1, ?_, ?_⟩
  · simpa only [measureReal_def, measure_sdiff_null hNzero] using hpFR
  · intro ω hω lam hlam
    have hid : ∀ lam ∈ regGrid ρ n,
        inputL2Norm V.law (q lam ω) =
          inputL2Norm (V.law.map V.zOf)
            (rHat n ω - estimatedOperator V mu gHat n ω (candidate lam ω)) ∧
        blockAverage V P sample (split.cal n) (fun w => q lam ω w ^ 2) ω =
          rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate lam ω) := by
      by_contra hbad
      exact hω.2 (hsub hbad)
    obtain ⟨hg, hr, hpilot, hcandidate⟩ := hFit ω hω.1.1
    obtain ⟨hh, hop⟩ := hcandidate lam hlam
    have hb := hBernstein ω hω.1.2 lam hlam
    rw [(hid lam hlam).1, (hid lam hlam).2] at hb
    exact iter_rdiv_calibration_comparison_of_nuisance_bounds V mu G g₀ gHat rHat
      support B c₀ CG (4 * B + 8 * B ^ 2 + 3) hIV hRange hDensity hBounds hHyp
      hB (by positivity) n ω (candidate lam ω) _ _ ν hg hh hr (Real.sqrt_nonneg _)
      hRadius hpilot hop hb

/-- Assume [density realizability](hyp:hDensity), [density bounds](hyp:hBounds),
[the hypothesis envelope B](hyp:hHyp), [nonnegative B](hyp:hB), [a coherent
selected pilot version](hyp:hPilotVersion), [the pilot envelope B](hyp:hPilotBound),
[positive sample size](hyp:hn), [almost-sure density membership](hyp:hg), and
[almost-sure candidate membership throughout the penalty grid](hyp:hCandidate).
If [the operator representatives are jointly measurable from training data and
instrument values](hyp:hop) and [agree with the selected operators both in
population and at every calibration observation](hyp:hOpCoherent), then [there
exists a training-measurable residual family bounded almost surely by 2 B on
fresh sections, whose population norm equals the actual fitted residual norm
and whose calibration-block squared average equals the original calibration
statistic, almost surely throughout the grid](goal).

Turn a coherent operator version into the actual calibration residual
version for any finite family of fitted candidates, including recursive ones.
Only class membership is used, not minimization of a zero-centered objective.
The sectionwise envelope comes from density normalization and PilotBounded;
the original empirical statistic is recovered using actual-block coherence. -/
-- @node: iter_rdiv_residual_version_of_operator_version
lemma iter_rdiv_residual_version_of_operator_version
    {pilotInputSupport : Set Z}
    (V : IVWorld W X Z) (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG ρ : ℝ)
    (n : ℕ) (candidate : ℝ → Ω → V.Hbar.toSubmodule)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hPilotVersion : RDIVSelectedPilotVersion V P sample split rHat)
    (hPilotBound : PilotBounded V P rHat pilotInputSupport B) (hn : 0 < n)
    (hg : ∀ᵐ ω ∂P, gHat n ω ∈ G)
    (hCandidate : ∀ᵐ ω ∂P, ∀ lam ∈ regGrid ρ n, candidate lam ω ∈ V.H)
    (op : ℝ → Ω → Z → ℝ)
    (hop : ∀ lam ∈ regGrid ρ n, @Measurable (Ω × Z) ℝ
      ((⨆ i ∈ split.pre n ∪ split.fit n,
        MeasurableSpace.comap (sample.Z i) inferInstance).prod inferInstance)
      inferInstance (fun p => op lam p.1 p.2))
    (hOpCoherent : ∀ᵐ ω ∂P, ∀ lam ∈ regGrid ρ n,
      (op lam ω =ᵐ[V.law.map V.zOf]
        estimatedOperator V mu gHat n ω (candidate lam ω)) ∧
      (∀ i ∈ split.cal n, op lam ω (V.zOf (sample.Z i ω)) =
        estimatedOperator V mu gHat n ω (candidate lam ω)
          (V.zOf (sample.Z i ω)))) :
    ∃ q : ℝ → Ω → W → ℝ,
      (∀ lam ∈ regGrid ρ n, @Measurable (Ω × W) ℝ
        ((⨆ i ∈ split.pre n ∪ split.fit n,
          MeasurableSpace.comap (sample.Z i) inferInstance).prod inferInstance)
        inferInstance (fun p => q lam p.1 p.2)) ∧
      (∀ lam ∈ regGrid ρ n, ∀ᵐ training ∂P,
        ∀ᵐ w ∂V.law, |q lam training w| ≤ 2 * B) ∧
      (∀ᵐ ω ∂P, ∀ lam ∈ regGrid ρ n,
        inputL2Norm V.law (q lam ω) =
          inputL2Norm (V.law.map V.zOf)
            (rHat n ω - estimatedOperator V mu gHat n ω (candidate lam ω)) ∧
        blockAverage V P sample (split.cal n) (fun w => q lam ω w ^ 2) ω =
          rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate lam ω)) := by
  obtain ⟨rBar, hrBar, R, hR, hRae, hrcoh⟩ :=
    rdiv_pilot_calibration_version V P sample split rHat B hPilotVersion hPilotBound n hn
  let q : ℝ → Ω → W → ℝ := fun lam ω w =>
    rBar (ω, V.zOf w) - op lam ω (V.zOf w)
  refine ⟨q, ?_, ?_, ?_⟩
  · intro lam hlam
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
      hrBar.comp ((measurable_fst.mono le_rfl hpre).prodMk measurable_snd)
    exact (hp.sub (hop lam hlam)).comp
      (measurable_fst.prodMk (V.measurable_z.comp measurable_snd))
  · intro lam hlam
    filter_upwards [hg, hCandidate, hRae, hOpCoherent] with ω hgω hcω hrω hoω
    have hb := rdiv_hypothesis_density_operator_bounded V mu G g₀ (gHat n ω)
      support B c₀ CG hDensity hBounds hHyp hB hgω
    have hz : ∀ᵐ z ∂V.law.map V.zOf,
        |rBar (ω, z) - op lam ω z| ≤ 2 * B := by
      filter_upwards [(hrcoh ω hrω).2.1, hb, (hoω lam hlam).1] with z hrz hTz heq
      rw [heq]
      exact (abs_sub _ _).trans (by
        have hT := hTz (candidate lam ω) (hcω lam hlam)
        change |estimatedOperator V mu gHat n ω (candidate lam ω) z| ≤ B at hT
        linarith only [hrz, hT])
    exact ae_of_ae_map V.measurable_z.aemeasurable hz
  · filter_upwards [hRae, hOpCoherent] with ω hrω hoω
    intro lam hlam
    constructor
    · unfold inputL2Norm
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
          filter_upwards [(hoω lam hlam).1, (hrcoh ω hrω).1] with z hz hrz
          simp only [hz, hrz, Pi.sub_apply])
    · unfold blockAverage rdivCalibrationStat
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp only [q, (hoω lam hlam).2 i hi, (hrcoh ω hrω).2.2 i hi]

/-- Under [the RDIV model](hyp:hIV), [density realizability](hyp:hDensity),
[density bounds](hyp:hBounds), [the hypothesis envelope B](hyp:hHyp), and
[nonnegative B](hyp:hB), suppose [the densities are likelihood maximizers](hyp:hMLE),
[selected densities have coherent versions](hyp:hDensityVersion), [the pilot
has a coherent version](hyp:hPilotVersion), [the pilot is bounded by B](hyp:hPilotBound),
and [the sample size is positive](hyp:hn). If [the grid-indexed candidates always
belong to the hypothesis class](hyp:hCandidate) and [are measurable from the
training data](hyp:hMeas), then [a jointly training-measurable residual family
exists, bounded almost surely by 2 B on fresh sections, whose population norms
equal the actual fitted residual norms and whose calibration-block squared
averages equal the original calibration statistics almost surely on the whole
penalty grid](goal).

Construct the calibration residual for the actual training-measurable
family. The operator is built locally from its L2 selection and the approved
density version, then the pilot version supplies the residual and its envelope.
This applies directly to each final fitted iterate; no empirical minimizer
with a different penalty center is substituted. -/
-- @node: iter_rdiv_calibration_residual_version
lemma iter_rdiv_calibration_residual_version
    {pilotInputSupport : Set Z}
    (V : IVWorld W X Z) (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : AnalysisSample V P) (split : SampleSplit)
    (mu : Measure X) (G : Set (X → Z → ℝ)) (g₀ : X → Z → ℝ)
    (gHat : ℕ → Ω → X → Z → ℝ) (rHat : ℕ → Ω → Z → ℝ)
    (support : Set (X × Z)) (B c₀ CG ρ : ℝ)
    (n : ℕ) (candidate : ℝ → Ω → V.Hbar.toSubmodule)
    (hIV : RDIVSetting V mu g₀)
    (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat)
    (hPilotVersion : RDIVSelectedPilotVersion V P sample split rHat)
    (hPilotBound : PilotBounded V P rHat pilotInputSupport B) (hn : 0 < n)
    (hCandidate : ∀ lam ∈ regGrid ρ n, ∀ ω, candidate lam ω ∈ V.H)
    (hMeas : ∀ lam ∈ regGrid ρ n, @Measurable Ω V.Hbar.toSubmodule
      (⨆ i ∈ split.pre n ∪ split.fit n,
        MeasurableSpace.comap (sample.Z i) inferInstance) (borel _) (candidate lam)) :
    ∃ q : ℝ → Ω → W → ℝ,
      (∀ lam ∈ regGrid ρ n, @Measurable (Ω × W) ℝ
        ((⨆ i ∈ split.pre n ∪ split.fit n,
          MeasurableSpace.comap (sample.Z i) inferInstance).prod inferInstance)
        inferInstance (fun p => q lam p.1 p.2)) ∧
      (∀ lam ∈ regGrid ρ n, ∀ᵐ training ∂P,
        ∀ᵐ w ∂V.law, |q lam training w| ≤ 2 * B) ∧
      (∀ᵐ ω ∂P, ∀ lam ∈ regGrid ρ n,
        inputL2Norm V.law (q lam ω) =
          inputL2Norm (V.law.map V.zOf)
            (rHat n ω - estimatedOperator V mu gHat n ω (candidate lam ω)) ∧
        blockAverage V P sample (split.cal n) (fun w => q lam ω w ^ 2) ω =
          rdivCalibrationStat V P sample split mu gHat rHat n ω (candidate lam ω)) := by
  obtain ⟨op, hop, N, hN, hNae, hcoh⟩ :=
    rdiv_selected_family_operator_calibration_version V P sample split mu G g₀ gHat
      support B c₀ CG ρ candidate hIV hDensity hBounds hHyp hMLE hDensityVersion
      n hn hCandidate hMeas
  exact iter_rdiv_residual_version_of_operator_version V P sample split mu G g₀
    gHat rHat support B c₀ CG ρ n candidate hDensity hBounds hHyp hB
    hPilotVersion hPilotBound hn ((hMLE n hn).1.mono fun _ h => h.1)
    (ae_of_all _ fun ω lam hlam => hCandidate lam hlam ω) op hop
    (hNae.mono fun ω hω => hcoh ω hω)

end Papers.TsAdaptiveEstimationInference
