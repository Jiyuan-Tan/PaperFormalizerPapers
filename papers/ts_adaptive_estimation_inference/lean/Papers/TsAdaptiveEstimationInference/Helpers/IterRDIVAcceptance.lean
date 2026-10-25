module
public import Papers.TsAdaptiveEstimationInference.Helpers.IterRDIV
public import Papers.TsAdaptiveEstimationInference.Helpers.RDIVDensityReduction
/-! Terminal calibration and deterministic stopping for iterative RDIV. -/
public section
set_option linter.unusedSectionVars false
namespace Papers.TsAdaptiveEstimationInference
open MeasureTheory Filter

-- @node: iter_rdiv_noise_dominates
/-- If [the iteration multiplier is at least one](hyp:ha) and [the penalty is positive](hyp:hlam), [the iterative RDIV noise threshold is at least the one-step RDIV threshold](goal). -/
lemma iter_rdiv_noise_dominates (a δ ν lam : ℝ) (ha : 1 ≤ a) (hlam : 0 < lam) :
    rdivNoiseLevel δ ν lam ≤ iterRdivNoiseLevel a δ ν lam := by
  unfold rdivNoiseLevel iterRdivNoiseLevel iterRdivScale
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ hlam.le
  nlinarith only [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg δ)]

-- @node: iter_rdiv_search_of_terminal_bound
/-- Suppose [the grid ratio lies in `[1/2, 1)`](hyp:hρ), [the failure probability lies strictly between zero and one](hyp:hξ), [the iteration multiplier is at least one](hyp:ha), [the sample size meets the bounded-envelope minimum](hyp:hn), [δ dominates the public logarithmic scale](hyp:hfloor), and [the terminal calibration statistic is at most 4B²](hyp:hD). [The discrepancy search accepts, its iteration cost is at most t times the terminal grid length, and its selected index is either zero or positive with the adjacent discrepancy relation at the selected penalty](goal). -/
lemma iter_rdiv_search_of_terminal_bound (ρ ξ B a δ ν : ℝ) (t n : ℕ)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (ha : 1 ≤ a) (hn : rdivMinSampleSize B ≤ n) (D : ℝ → ℝ)
    (hfloor : rdivPublicLogScale ρ ξ n ≤ δ)
    (hD : D (gridValue ρ (terminalIndex ρ n)) ≤ 4 * B ^ 2) :
    Accepts ρ n D (iterRdivNoiseLevel a δ ν) ∧
      t * (discrepancyIndex ρ n D (iterRdivNoiseLevel a δ ν) + 1) ≤
        t * (terminalIndex ρ n + 1) ∧
      (discrepancyIndex ρ n D (iterRdivNoiseLevel a δ ν) = 0 ∨
        (0 < discrepancyIndex ρ n D (iterRdivNoiseLevel a δ ν) ∧
          AdjacentDiscrepancyRelation ρ
            (selectedPenalty ρ n D (iterRdivNoiseLevel a δ ν))
            D (iterRdivNoiseLevel a δ ν))) := by
  have hl : 0 < gridValue ρ (terminalIndex ρ n) :=
    mul_pos (by norm_num) (pow_pos (by linarith [hρ.1]) _)
  have hthreshold := rdiv_terminal_threshold_bound ρ ξ B δ ν hρ hξ n hn hfloor
  have hnoise := iter_rdiv_noise_dominates a δ ν _ ha hl
  have hAccept : Accepts ρ n D (iterRdivNoiseLevel a δ ν) := by
    refine ⟨terminalIndex ρ n, le_rfl, ?_⟩
    exact hD.trans (hthreshold.trans (mul_le_mul_of_nonneg_left hnoise (by norm_num)))
  obtain ⟨hi, hcases⟩ := discrepancyIndex_first_acceptance ρ n D _ hρ hAccept
  exact ⟨hAccept, Nat.mul_le_mul_left t (Nat.add_le_add_right hi 1), hcases⟩

variable {𝒲 𝒳 𝒵 Ω : Type*} [MeasurableSpace 𝒲] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒵] [MeasurableSpace Ω]
  {pilotInputSupport : Set 𝒵}
  (V : IVWorld 𝒲 𝒳 𝒵) (P : Measure Ω) [IsProbabilityMeasure P]
  (sample : AnalysisSample V P) (split : SampleSplit)

-- @node: iter_rdiv_calibrated_public_log_floor
/-- If [the failure probability lies strictly between zero and one](hyp:hξ), [the density critical-radius bound holds](hyp:hG), [the hypothesis critical-radius bound holds](hyp:hH), [the base accuracy curves satisfy the iteration-scale calibration](hyp:hscale), [the public curves are valid calibrated inflations of the base curves](hyp:hinflate), and [the sample size is positive](hyp:hn), [the public density accuracy dominates the public logarithmic scale](goal). -/
lemma iter_rdiv_calibrated_public_log_floor (mu : Measure 𝒳)
    (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
    (ρ ξ : ℝ) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (rawG rawH rawR : ℕ → ℝ → ℝ) (δ ν baseδ baseν : ℕ → ℝ)
    (κδ κν required : ℝ) (t : ℕ)
    (hG : DensityCriticalRadiusBound V G g₀ rawG)
    (hH : HypothesisCriticalRadiusBound V mu G rawH ρ)
    (hscale : RDIVIterationScaleCalibration ρ ξ baseδ baseν
      (rdivEvaluatedAccuracy rawG) (rdivEvaluatedAccuracy rawH)
      (rdivEvaluatedAccuracy rawR) t)
    (hinflate : CalibratedValidBounds δ ν baseδ baseν κδ κν required)
    (n : ℕ) (hn : 0 < n) : rdivPublicLogScale ρ ξ n ≤ δ n := by
  have ht : (1 : ℝ) ≤ t := by exact_mod_cast hscale.1
  have ht0 : (0 : ℝ) < t := by linarith
  have hquarter : ξ / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hξ.1, hξ.2]
  have hbudget : ξ / (4 * t) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos hξ.1 (mul_pos (by norm_num) ht0)
    · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * t)).2
      linarith [hξ.2]
  have hg := (hG n hn (ξ / 4) hquarter).1.le
  have hh := (hH n hn (ξ / (4 * t)) hbudget).1.1.le
  have heq : gridConfidence ρ (ξ / (4 * t)) n = iterGridConfidence ρ ξ n t / 4 := by
    unfold gridConfidence iterGridConfidence
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq] at hh
  have hs := (hscale.2.1 n hn).1
  change rawG n (ξ / 4) + rawH n (iterGridConfidence ρ ξ n t / 4) +
    rdivPublicLogScale ρ ξ n ≤ baseδ n at hs
  have hf : rdivPublicLogScale ρ ξ n ≤ baseδ n := by linarith only [hg, hh, hs]
  have hb : 0 ≤ baseδ n := (Real.sqrt_nonneg _).trans hf
  have hδ : baseδ n ≤ δ n := by
    rw [hinflate.2.2.2.2.1 n]
    nlinarith only [hinflate.1, hb]
  exact hf.trans hδ

-- @node: iter_rdiv_zero_envelope_initial_index
/-- If [the iteration multiplier is at least one](hyp:ha), [the oracle penalty is at most two](hyp:horacle), [the iterative discrepancy envelope holds on E with zero source vector](hyp:henv), and [the sample outcome belongs to E](hyp:hω), [the discrepancy search accepts at its initial index zero](goal). -/
lemma iter_rdiv_zero_envelope_initial_index (mu : Measure 𝒳)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (ρ c a β : ℝ) (t : ℕ) (δ ν : ℕ → ℝ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (n : ℕ) (E : Set Ω) (C : ℝ) (ha : 1 ≤ a)
    (horacle : iterRdivOraclePoint ρ c a β t δ ν n ≤ 2)
    (henv : IterRDIVDiscrepancyOn V P sample split mu gHat rHat
      ρ c a β t δ ν 0 iter n E C) (ω : Ω) (hω : ω ∈ E) :
    discrepancyIndex ρ n
      (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω
        (iter n t lam ω)) (iterRdivNoiseLevel a (δ n) (ν n)) = 0 := by
  have hgrid : (2 : ℝ) ∈ regGrid ρ n := by
    exact Finset.mem_image.mpr
      ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _), by simp [gridValue]⟩
  have hb := henv.2 ω hω 2 hgrid ⟨horacle, le_rfl⟩
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero] at hb
  have hnoise : 0 ≤ iterRdivNoiseLevel a (δ n) (ν n) 2 := by
    unfold iterRdivNoiseLevel iterRdivScale
    have ha0 : 0 ≤ a := by linarith
    positivity
  have hi : rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t 2 ω) ≤
      3 / 2 * iterRdivNoiseLevel a (δ n) (ν n) 2 := by
    linarith only [hb, hnoise]
  have he : ∃ k ≤ terminalIndex ρ n,
      rdivCalibrationStat V P sample split mu gHat rHat n ω
        (iter n t (gridValue ρ k) ω) ≤
          3 / 2 * iterRdivNoiseLevel a (δ n) (ν n) (gridValue ρ k) := by
    refine ⟨0, Nat.zero_le _, ?_⟩
    simpa only [gridValue, pow_zero, mul_one] using hi
  unfold discrepancyIndex
  rw [dif_pos he]
  exact Nat.le_zero.mp (Nat.find_min' he (by
    simpa only [gridValue, pow_zero, mul_one] using And.intro (Nat.zero_le _) hi))

-- @node: iter_rdiv_calibration_bounded_event
/-- Assume [the IV sampling and density identities](hyp:hIV), [density realizability](hyp:hDensity), [the density bounds on the designated support](hyp:hBounds), [the hypothesis envelope B on that support](hyp:hHyp), [nonnegative B](hyp:hB), [the pilot regression rate](hyp:hPilot), [the pilot envelope B](hyp:hPilotBound), [selected likelihood maximization](hyp:hMLE), [the selected-density version condition](hyp:hSelectedDensityVersion), [the selected-pilot version condition](hyp:hSelectedPilotVersion), and [attainment of the iterative empirical minima](hyp:hMinima), with [at least one iteration](hyp:ht) and [positive sample size](hyp:hn). [There is a measurable probability-one event on which the final iterate's calibration statistic is at most 4B² simultaneously over the entire regularization grid](goal). -/
lemma iter_rdiv_calibration_bounded_event
    (mu : Measure 𝒳) (G : Set (𝒳 → 𝒵 → ℝ)) (g₀ : 𝒳 → 𝒵 → ℝ)
    (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ) (rHat : ℕ → Ω → 𝒵 → ℝ)
    (support : Set (𝒳 × 𝒵)) (B c₀ CG ρ : ℝ)
    (δr : ℕ → ℝ → ℝ) (t : ℕ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hIV : RDIVSetting V mu g₀) (hDensity : DensityRealizable V mu G g₀)
    (hBounds : DensityBounds G g₀ support c₀ CG)
    (hHyp : HypothesisClassBounded V support B) (hB : 0 ≤ B)
    (hPilot : PilotRegressionRate V P sample split rHat δr)
    (hPilotBound : PilotBounded V P rHat pilotInputSupport B)
    (hMLE : MLEMaximizerSelected V P sample split G gHat)
    (hSelectedDensityVersion : RDIVSelectedDensityVersion V P sample split mu gHat)
    (hSelectedPilotVersion : RDIVSelectedPilotVersion V P sample split rHat)
    (hMinima : IterRDIVMinimaAttained V P sample split mu gHat ρ t iter)
    (ht : 1 ≤ t) (n : ℕ) (hn : 0 < n) :
    ∃ E : Set Ω, MeasurableSet E ∧ (∀ᵐ ω ∂P, ω ∈ E) ∧
      ∀ ω ∈ E, ∀ lam ∈ regGrid ρ n,
        rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω) ≤
          4 * B ^ 2 := by
  obtain ⟨S, hS, hSae, hSgood⟩ := rdiv_density_calibration_event
    (hSelectedDensityVersion := hSelectedDensityVersion) V P sample split
    mu G g₀ gHat support c₀ CG hIV hDensity hBounds hMLE n hn
  obtain ⟨R, hR, hRae, hRgood⟩ := rdiv_pilot_calibration_event
    (hSelectedPilotVersion := hSelectedPilotVersion) V P sample split
    rHat δr B hPilot hPilotBound n hn
  refine ⟨S ∩ R, hS.inter hR, ?_, ?_⟩
  · filter_upwards [hSae, hRae] with ω hωS hωR
    exact ⟨hωS, hωR⟩
  · intro ω hω lam hlam
    exact rdiv_calibration_stat_le_four_of_density V P sample split
      mu G g₀ gHat rHat support B c₀ CG hDensity hBounds hHyp hB n hn ω
      (hSgood ω hω.1).1 (iter n t lam ω)
      ((hMinima n hn lam hlam).1.2 t ht le_rfl ω).1
      (hRgood ω hω.2) (hSgood ω hω.1).2

-- @node: iter_rdiv_acceptance_event_intersection
/-- Suppose [the grid ratio lies in `[1/2, 1)`](hyp:hρ), [the failure probability lies strictly between zero and one](hyp:hξ), [the iteration multiplier is at least one](hyp:ha), [the sample size meets the bounded-envelope minimum](hyp:hn), and [δ dominates the public logarithmic scale](hyp:hfloor). If [E is measurable](hyp:hE), [S is measurable](hyp:hS), [E has probability at least 1−ξ](hyp:hpE), [S has probability one](hyp:hSae), and [the calibration statistic is at most 4B² on S throughout the grid](hyp:hbound), [their intersection is measurable with probability at least 1−ξ, and on it the search accepts within t times the terminal grid length, either at index zero or at a positive index satisfying the adjacent discrepancy relation](goal). -/
lemma iter_rdiv_acceptance_event_intersection
    (mu : Measure 𝒳) (gHat : ℕ → Ω → 𝒳 → 𝒵 → ℝ)
    (rHat : ℕ → Ω → 𝒵 → ℝ) (ρ ξ B a δ ν : ℝ) (t n : ℕ)
    (iter : ℕ → ℕ → ℝ → Ω → V.Hbar.toSubmodule)
    (hρ : ρ ∈ Set.Ico (1 / 2 : ℝ) 1) (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1)
    (ha : 1 ≤ a) (hn : rdivMinSampleSize B ≤ n)
    (hfloor : rdivPublicLogScale ρ ξ n ≤ δ)
    (E S : Set Ω) (hE : MeasurableSet E) (hS : MeasurableSet S)
    (hpE : 1 - ξ ≤ P.real E) (hSae : ∀ᵐ ω ∂P, ω ∈ S)
    (hbound : ∀ ω ∈ S, ∀ lam ∈ regGrid ρ n,
      rdivCalibrationStat V P sample split mu gHat rHat n ω (iter n t lam ω) ≤
        4 * B ^ 2) :
    MeasurableSet (E ∩ S) ∧ 1 - ξ ≤ P.real (E ∩ S) ∧
      ∀ ω ∈ E ∩ S,
        Accepts ρ n
          (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω
            (iter n t lam ω)) (iterRdivNoiseLevel a δ ν) ∧
        t * (discrepancyIndex ρ n
          (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω
            (iter n t lam ω)) (iterRdivNoiseLevel a δ ν) + 1) ≤
          t * (terminalIndex ρ n + 1) ∧
        (discrepancyIndex ρ n
          (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω
            (iter n t lam ω)) (iterRdivNoiseLevel a δ ν) = 0 ∨
          (0 < discrepancyIndex ρ n
            (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω
              (iter n t lam ω)) (iterRdivNoiseLevel a δ ν) ∧
            AdjacentDiscrepancyRelation ρ
              (selectedPenalty ρ n
                (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω
                  (iter n t lam ω)) (iterRdivNoiseLevel a δ ν))
              (fun lam => rdivCalibrationStat V P sample split mu gHat rHat n ω
                (iter n t lam ω)) (iterRdivNoiseLevel a δ ν))) := by
  refine ⟨hE.inter hS, ?_, ?_⟩
  · have heq : (E ∩ S : Set Ω) =ᵐ[P] E := by
      filter_upwards [hSae] with ω hω
      exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩
    rwa [measureReal_congr heq]
  · intro ω hω
    apply iter_rdiv_search_of_terminal_bound ρ ξ B a δ ν t n hρ hξ ha hn _ hfloor
    exact hbound ω hω.2 _ (Finset.mem_image.mpr
      ⟨terminalIndex ρ n, Finset.mem_range.mpr (Nat.lt_succ_self _), rfl⟩)

end Papers.TsAdaptiveEstimationInference
